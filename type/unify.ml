open Core
open Common
open Common.Util
open Type
(* open TypeVar *)
open TypeOperations

(********************************************
 * Unify monad 
 ********************************************)
type unify_error =
  | NoMatch
  | NoMatchKind
  | NoMatchPred
  | NoSubsume
  | NoEntail
  | Infinite
  | NoArgMatch of int * int

type st = { uniq : int; sub : TypeVar.sub }
type 'a res =
  | Ok of 'a * st
  | Err of unify_error * st

(* TODO: this might need to be lazy *)
(* module rec UnifyM : Monadic.S with type 'a t = (st -> 'a res) = struct
 *   type 'a t = (st -> 'a res)
 *   let return (x:'a) : 'a t = fun st -> Ok(x,st)
 *   let bind (u:'a t) (f: 'a -> 'b t) : 'b t = fun st1 ->
 *     match u st1 with
 *     | Ok(x,st2) -> (f x) st2
 *     | Err(err,st2) -> Err(err,st2)
 * end *)
module UnifyM_ = struct
  type 'a t = (st -> 'a res)
  let return (x:'a) : 'a t = fun st -> Ok(x,st)
  let bind (u:'a t) ~(f: 'a -> 'b t) : 'b t = fun st1 ->
    match u st1 with
    | Ok(x,st2) -> (f x) st2
    | Err(err,st2) -> Err(err,st2)
  let map a ~f = bind a ~f:(return <.> f)
end
module UnifyM = struct
  module M = Common.Monadic.Make(UnifyM_)
  include M
  module Let_syntax = M
  let error err = fun (st:'a) -> Err(err,st)
  let get_subst = fun (st:'a) -> Ok(st.sub, st)
  let subst (x:typ) : typ t = get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_typ.(sub |-> x)
  let subst_list (x:typ list) : typ list t = get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> x)
end
(* let unify_error err : 'a t = fun st -> Err(err,st) *)
(* let (>>=) = bind *)

(* TODO: All of these should take positions as the first arguments *)

(** Do two types overlap on the argument types? Used to check for overlapping
  * definitions of overloaded identifiers. *)
let overlaps (free:TypeVar.TVSet.t) (tp1:typ) (tp2:typ) : unit UnifyM.t =
  let rho1 = instantiate tp1 in
  let rho2 = instantiate tp2 in
  match (split_fun_type rho1, split_fun_type rho2) with
  (* values always overlap *)
  | (None,_) -> UnifyM.return ()
  | (_,None) -> UnifyM.return ()
  (* rest *)
  | (Some(targs1,_,_),Some(targs2,_,_)) ->
      let (fixed1,optional1) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs1) in
      let (fixed2,optional2) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs2) in
      let hi = Pervasives.max (List.length fixed1) (List.length fixed2) in
      let fo1 = (flip List.take) hi (fixed1 @ (List.map ~f:unoptional optional1)) in
      let fo2 = (flip List.take) hi (fixed2 @ (List.map ~f:unoptional optional1)) in
      if ((List.length fo1) <> (List.length fo2)) then
        UnifyM.error NoMatch     (* one has more fixed arguments than the other can ever get *)
      else UnifyM.return ()

(** Does a type have the given named arguments *)
let match_named (tp:typ) (n:int) (named : Name.name list) : unit UnifyM.t =
  let rho1 = instantiate tp in
  match split_fun_type rho1 with
  | None -> UnifyM.error NoMatch
  | Some(pars,_,_) ->
      if (n + List.length named) > List.length pars then
        UnifyM.error NoMatch
      else
        let npars = List.drop pars n in
        let names = List.map ~f:fst npars in
        if List.for_all ~f:(List.mem names ~equal:Name.eq_name) named then
          (* [tp | (nm,tp) <- npars, not (nm `elem` named)] *)
          let rest = List.(npars >>= fun (nm,tp) ->
                           guard (not @@ mem named nm ~equal:Name.eq_name) >>= fun _ ->
                           return tp)
          in 
          if (List.for_all ~f:is_optional rest) then
            UnifyM.return ()
          else UnifyM.error NoMatch
        else UnifyM.error NoMatch


let extract_normalize_effect (tp:typ) : (typ list * typ) UnifyM.t = let open UnifyM in
  let%bind tp' = (get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_typ.(sub |-> tp)) in
  return @@ extract_ordered_effect tp'

let rec unify (t1:typ) (t2:typ) : unit UnifyM.t = let open UnifyM in match (t1,t2) with
  | TApp(TCon tc1, _), TApp(TCon tc2, _)
    when tc2 = tcon_effect_extend &&  tc1 = tcon_effect_extend ->
      unify_effect t1 t2
        
  (* | TApp(TCon tc1, _), TVar tv2 when tc1 = tcon_effect_extend && is_meta tv2 ->
   *     unify_effect_var tv2 t1
   *       
   * | TVar tv1, TApp(TCon tc2, _) when tc2 = tcon_effect_extend && is_meta tv1 ->
   *     unify_effect_var tv1 t2
   * 
   * (\* Type variables *\)
   * | (TVar v1, TVar v2) when v1 = v2 -> return ()
   * | (TVar tv, tp) when is_meta tv -> unify_tvar tv tp
   * | (tp, TVar tv) when is_meta tv -> unify_tvar tv tp *)

  (* Constants *)
  | TCon tc1, TCon tc2 when tc1 = tc2 -> return ()

  (* Applications *)
  | TApp(t, ts), TApp(u, us) when (List.length ts) = (List.length us) ->
      unify t u >>
      unifies ts us

  (* Functions *)
  | TFun(a1,e1,r1), TFun(a2,e2,r2) when (List.length a1) = (List.length a2) ->
      unify e1 e2 >>
      unifies (r1::(List.map ~f:snd a1)) (r2::(List.map ~f:snd a2))
        
  | _ -> assert false

and unifies (tl1:typ list) (tl2:typ list) = let open UnifyM in match (tl1,tl2) with
  | [], [] -> UnifyM.return ()
  | t::ts, u::us ->
      let%bind st = subst t in
      let%bind su = subst u in 
      unify st su >>
      unifies ts us

  | _ -> Failure.failure "Type.Unify.unifies"

and unify_effect (tp1:typ) (tp2:typ) = let open UnifyM in 
  let%bind (ls1, tl1) = extract_normalize_effect tp1 in
  let%bind (ls2, tl2) = extract_normalize_effect tp2 in
  let%bind (ds1,ds2)  = unify_labels ls1 ls2 in
  match (expand_syn tl1, expand_syn tl2) with
  | (TVar{type_var_id=id1; type_var_kind=kind1; type_var_flavour=Meta},
     TVar{type_var_id=id2; type_var_kind=kind2; type_var_flavour=Meta}) when
      id1 = id2 && not (List.is_empty ds1 && List.is_empty ds2) -> error Infinite
  | _ ->
      let%bind tail1 = (if List.is_empty ds1 then return tl1 else
                          let tv1 = freshTVar Kind.kind_effect Kind.Meta in
                          unify tl1 (effect_extends ds1 tv1) >> return tv1) in
      let%bind stl2 = subst tl2 in
      let%bind tail2 = (if List.is_empty ds2 then return stl2 else
                          let tv2 = freshTVar Kind.kind_effect Kind.Meta in
                          unify stl2 (effect_extends ds2 tv2) >> return tv2) in
      let%bind stail1 = subst tail1 in
      unify stail1 tail2 >>
      let%bind stp1 = subst tp1 in
      let%bind stp2 = subst tp2 in
      return ()
    

and unify_labels (ls1:tau list) (ls2:tau list) : (tau list * tau list) UnifyM.t = let open UnifyM in
  match (ls1,ls2) with
  | [], [] -> return ([],[])
  | (_::_, []) -> return ([],ls1)
  | ([], _::_) -> return (ls2,[])
  | (l1::ll1, l2::ll2) ->
      if (Name.compare_name (label_name l1) (label_name l2) < 0) then
        let%bind (ds1,ds2) = unify_labels ll1 ls2 in
        return (ds1, l1::ds2)
      else if (Name.compare_name (label_name l1) (label_name l2) > 0) then
        let%bind (ds1,ds2) = unify_labels ls1 ll2 in
        return (l2::ds1, ds2)
      else
        unify l1 l2 >>
        let%bind ll1' = (get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> ll1)) in
        let%bind ll2' = (get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> ll2)) in
        unify_labels ll1 ll2

(**
 * @entails skolems known preds@ returns both predicates that need to be proved
 * and a core transformer that applies the evidence for @preds@ and abstracts for
 * those in @known@. The @preds@ are entailed by
 * @known@ and predicates containing a type variable in @skolems@ must be entailed
 * completely by other predicates (not containing such skolems). *)
let rec entails (skolems:TypeVar.TVSet.t) (known:evidence list) = function
  | [] -> UnifyM.return ([],id)
  (* TODO: possible failure point here *)
  | evs when List.equal ~equal:Type.Eq_pred.equal
               (List.map ~f:(fun e -> e.ev_pred) known)
               (List.map ~f:(fun e -> e.ev_pred) evs) ->
      UnifyM.return (evs,id)
  | ev::evs -> match ev.ev_pred with
    | PredIFace(name,[_;_;_]) when name = Name_prim.name_pred_heap_div -> (* can always be solved *)
        entails skolems known evs
    | _ -> UnifyM.error NoEntail
             
(**
 * `subsume free t_1 t_2` holds if $t_2$ can be instantiated to $t_1$ where
 * `free` are the free type variables in the assumptnio. Returns under
 * which predicates this holds and a core transformer that needs to be applied
 * to the expressions of type $t_2$. Also returns a new type for the expect type 
 * $t_1$ where 'some' types have been properly substitude (and may be quantified) *)
let subsume (free:TypeVar.TVSet.t) (tp1:typ) (tp2:typ)
  : (typ * evidence list * (Heart.expr -> Heart.expr)) UnifyM.t = let open UnifyM in
  (* skolemize, instantiate, and unify *)
  let (sks, evs1, rho1, core1) = skolemize_ex tp1 in
  let (tvs, evs2, rho2, core2) = instantiate_ex tp2 in
  unify rho2 rho1 >>
    
(* Escape check: no skolems should escape into the environment
 * Entailment check: predicates should be entailed
 * TODO: we should check for skolems since predicates with skolems must be entailed directly *)
  let%bind subst = get_subst in begin
    let allfree = TypeVar.tvs_union free (TypeVar.HasTypeVar_typ.ftv tp1) in 
    let escaped = (* fsv $ [tp  | (tv,tp) <- subList sub, tvsMember tv allfree]  *)
      TypeVar.tvs_filter ~f:is_skolem @@ TypeVar.HasTypeVar_list_typ.ftv @@
      List.(TypeVar.sub_list subst >>= fun (tv,tp) ->
            guard (TypeVar.tvs_member allfree tv) >>= fun _ ->
            return tp)
    in 
    (if (TypeVar.tvs_disjoint (TypeVar.tvs_new sks) escaped)
     then return () else error NoSubsume)
  end >>
  let%bind (evs_ent, core_ent) = entails (TypeVar.tvs_new sks) HasTypeVar_evidence_list.(subst |-> evs1) HasTypeVar_evidence_list.(subst |-> evs2) in
  let (vars, ssub) = fresh_sub Bound sks in
  let subx = TypeVar.(ssub @@@ subst) in
  let tp = quantify_type vars @@
    qualify_type
      (List.map evs1 ~f:(fun {ev_pred} -> TypeVar.HasTypeVar_pred.(subx |-> ev_pred)))
      TypeVar.HasTypeVar_typ.(subx |-> rho1)
  in
  return (tp, HasTypeVar_evidence_list.(subx |-> evs_ent),
          fun expr ->
            Heart.add_type_lambdas vars @@                                   (* generalize *)
            Heart.HasTypeVar_expr.(subx |-> (core_ent @@                     (* apply evidence evs2 & abstract evidence evs1 *)
                                             Heart.add_type_apps tvs expr))) (* instantiate *)
    
  


(** Does a function type match the given arguments? If the first argument 'matchSome' is true,
 ** it is considered a match even if not all arguments to the function are supplied. *)
(* let match_arguments (match_some:bool) (\* (range:range) *\) (free:TypeVar.TVSet.t) (tp:typ) (fixed:typ list) (named:(Name.name * typ) list) : unit UnifyM.t =
 *   let rho1 = instantiate tp in
 *   match split_fun_type rho1 with
 *   | None -> UnifyM.error NoMatch
 *   | Some(pars,_,_) ->
 *       if ((List.length fixed) + (List.length named) > List.length pars) then
 *         UnifyM.error NoMatch
 *       else                      (\* subsume fixed parameters *\)
 *         let (fpars, npars) = List.split_n pars (List.length fixed) in
 *         UnifyM.mapM (fun (tpar,targ) -> subsume free (unoptional tpar) targ) (List.zip_exn (List.map ~f:snd fpars) fixed) *)
