open Core
open Common
open Common.Util
open Heart.Type
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

type st = TypeVar.sub           (* global state *)
type 'a res =
  | Ok of 'a * st
  | Err of unify_error * st

(* The unification state-monad *)
module UnifyM = struct
  module Let_syntax = struct
    type 'a t = (st -> 'a res)
    let return (x:'a) : 'a t = fun st -> Ok(x,st)
    let bind (u:'a t) ~(f: 'a -> 'b t) : 'b t = fun st1 ->
      match u st1 with
      | Ok(x,st2) -> (f x) st2
      | Err(err,st2) -> Err(err,st2)
    let map a ~f = bind a ~f:(return <.> f)
  end
  
  include Common.Monadic.Make(Let_syntax)

  let run f =
    match f TypeVar.sub_null with
    | Ok(x,sub) -> (Result.Ok x, sub)
    | Err(err,sub) -> (Result.Error err, sub)
  
  let error err = fun (st:'a) -> Err(err,st)
  let extend_sub tv tp = fun (st:'a) -> Ok((), TypeVar.sub_extend tv tp st)
  
  let get_subst = fun (st:'a) -> Ok(st, st)
  let subst (x:typ) : typ t = get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_typ.(sub |-> x)
  let subst_list (x:typ list) : typ list t = get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> x)
  let subst_pred (x:pred) : pred t = get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_pred.(sub |-> x)
end


(** Do two types overlap on the argument types? Used to check for overlapping
  * definitions of overloaded identifiers. *)
let overlaps (free:TypeVar.Set.t) (tp1:typ) (tp2:typ) : unit UnifyM.t =
  let rho1 = instantiate tp1 in
  let rho2 = instantiate tp2 in
  match (split_fun_type rho1, split_fun_type rho2) with
  (* values always overlap *)
  | (None,_) | (_,None) -> UnifyM.return ()
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
let match_named (tp:typ) (n:int) (named : Name.t list) : unit UnifyM.t =
  let rho1 = instantiate tp in
  match split_fun_type rho1 with
  | None -> UnifyM.error NoMatch
  | Some(pars,_,_) ->
      if (n + List.length named) > List.length pars then
        UnifyM.error NoMatch
      else
        let npars = List.drop pars n in
        let names = List.map ~f:fst npars in
        if List.for_all ~f:(List.mem names ~equal:Name.equal) named then
          (* [tp | (nm,tp) <- npars, not (nm `elem` named)] *)
          let rest = List.(npars >>= fun (nm,tp) ->
                           guard (not @@ mem named nm ~equal:Name.equal) >>= fun _ ->
                           return tp)
          in 
          if (List.for_all ~f:is_optional rest) then
            UnifyM.return ()
          else UnifyM.error NoMatch
        else UnifyM.error NoMatch

let rec match_kind kind1 kind2 : bool = match kind1, kind2 with
  | Heart.Kind.KCon(c1), Heart.Kind.KCon(c2) -> c1 = c2
  | Heart.Kind.KApp(a1,r1), Heart.Kind.KApp(a2,r2) -> (match_kind a1 a2) && (match_kind r1 r2)
  | _,_ -> false

let match_kinds kinds1 kinds2 : unit UnifyM.t =
  let matches = List.map2_exn ~f:match_kind kinds1 kinds2 in
  let all_match = List.fold ~init:true ~f:(&&) matches in
  if all_match then
    UnifyM.return ()
  else 
    UnifyM.error NoMatchKind

let extract_normalize_effect (tp:typ) : (typ list * typ) UnifyM.t = let open UnifyM in
  let%bind tp' = subst tp in
  return @@ extract_ordered_effect tp'

let rec unify (t1:typ) (t2:typ) : unit UnifyM.t = let open UnifyM in match (t1,t2) with
  | TApp(TCon tc1, _), TApp(TCon tc2, _)
    when tc2 = tcon_effect_extend &&  tc1 = tcon_effect_extend ->
      unify_effect t1 t2
        
  | TApp(TCon tc1, _), TVar tv2 when tc1 = tcon_effect_extend && is_meta tv2 ->
      unify_effect_var tv2 t1
        
  | TVar tv1, TApp(TCon tc2, _) when tc2 = tcon_effect_extend && is_meta tv1 ->
      unify_effect_var tv1 t2
  
  (* Type variables *)
  | (TVar v1, TVar v2) when v1 = v2 -> return ()
  | (TVar tv, tp) when is_meta tv -> unify_tvar tv tp
  | (tp, TVar tv) when is_meta tv -> unify_tvar tv tp

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

  (* quantified types *)
  | TForall(vars1, preds1, tp1), TForall(vars2, preds2, tp2)
    when (List.length vars1) = (List.length vars2) &&
         (List.length preds1) = (List.length preds2) ->
      let kinds1 = List.map ~f:TypeKind.get_kind_type_var vars1 in
      let kinds2 = List.map ~f:TypeKind.get_kind_type_var vars2 in
      match_kinds kinds1 kinds2 >>
      (* replace with shared bound variables in both types
       * NOTE: assumes ordered quantifiers and ordered predicates
       * NOTE: we don't use Skolem as a Meta variable can unify with a Skolem but not with a Bound one *)
      let vars = List.map ~f:(fun kind -> freshTVar kind Heart.Kind.Bound) kinds1 in
      let sub1 = TypeVar.sub_new @@ List.zip_exn vars1 vars in
      let sub2 = TypeVar.sub_new @@ List.zip_exn vars2 vars in
      let stp1 = TypeVar.HasTypeVar_typ.(sub1 |-> tp1) in
      let stp2 = TypeVar.HasTypeVar_typ.(sub2 |-> tp2) in
      let _spreds1 = TypeVar.HasTypeVar_list_pred.(sub1 |-> preds1) in
      let _spreds2 = TypeVar.HasTypeVar_list_pred.(sub2 |-> preds2) in
      (* and unify the results *)
      unify stp1 stp2 >>
      unify_preds preds1 preds2
      (* no need to check for escaping skolems as we don't unify to bound variables *)

  (*TODO: orig_line:247 cps translation/continuations stuff*)

  (* synonyms *)
  | TSyn(syn1,_,tp1), TSyn(syn2,_,_) when syn1.type_syn_rank >  syn2.type_syn_rank -> unify tp1 t2
  | TSyn(syn1,_,_), TSyn(syn2,_,tp2) when syn1.type_syn_rank <= syn2.type_syn_rank -> unify t1 tp2
  | TSyn(_,_,tp1), tp2 -> unify tp1 tp2
  | tp1, TSyn(_,_,tp2) -> unify tp1 tp2

    (* No match *)
  | _ -> error NoMatch

and unifies (tl1:typ list) (tl2:typ list) = let open UnifyM in match (tl1,tl2) with
  | [], [] -> UnifyM.return ()
  | t::ts, u::us ->
      let%bind st = subst t in
      let%bind su = subst u in 
      unify st su >>
      unifies ts us

  | _ -> failwith "Type.Unify.unifies"

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
                          let tv1 = freshTVar Heart.Kind.kind_effect Heart.Kind.Meta in
                          unify tl1 (effect_extends ds1 tv1) >> return tv1) in
      let%bind stl2 = subst tl2 in
      let%bind tail2 = (if List.is_empty ds2 then return stl2 else
                          let tv2 = freshTVar Heart.Kind.kind_effect Heart.Kind.Meta in
                          unify stl2 (effect_extends ds2 tv2) >> return tv2) in
      let%bind stail1 = subst tail1 in
      unify stail1 tail2 >>
      let%bind stp1 = subst tp1 in
      let%bind stp2 = subst tp2 in
      return ()

and unify_effect_var tv1 tp2  = let open UnifyM in
  let (ls2, tl2) = extract_ordered_effect tp2 in (* ls2 must be non-empty *)
  match expand_syn tl2 with
  | TVar tv2 when tv1 = tv2 ->  (* e ~ <div,exn|e> ~> e := <div,exn|e'> *)
      error Infinite
  | _ ->
      (* let tv = freshTVar Heart.Kind.kind_effect Heart.Kind.Meta in *)
      unify_tvar tv1 (effect_extends ls2 tl2)

and unify_tvar (tv:type_var) (tp:typ) : unit UnifyM.t =
  if not (is_meta tv) then
    failwith "Type.Unify.unify_tvar: called with skolem or bound variable";

  let etp = expand_syn tp in
  if TypeVar.tvs_member (TypeVar.tvs_filter ~f:is_meta (TypeVar.HasTypeVar_typ.ftv etp)) tv then
    match expand_syn tp with
    | TVar tv2 when tv = tv2 -> UnifyM.return () (* i.e. a ~ id<a> *)
    | _ -> UnifyM.error Infinite
  else
    match etp with
    | TVar{type_var_flavour=Heart.Kind.Bound} -> UnifyM.error NoMatch (* can't unify with bound variables *)
    | TVar({type_var_id=id2; type_var_flavour=Heart.Kind.Meta} as tv2) when tv.type_var_id <= id2 ->
        if tv.type_var_id < id2 then
          unify_tvar tv2 (TVar tv)
        else
          UnifyM.return ()      (* TODO: kind check? *)
    | _ ->
        if not (match_kind tv.type_var_kind (TypeKind.get_kind_typ tp)) then
          UnifyM.error NoMatchKind
        else 
          UnifyM.(extend_sub tv tp >> return ())

and unify_labels (ls1:tau list) (ls2:tau list) : (tau list * tau list) UnifyM.t = let open UnifyM in
  match (ls1,ls2) with
  | [], [] -> return ([],[])
  | (_::_, []) -> return ([],ls1)
  | ([], _::_) -> return (ls2,[])
  | (l1::ll1, l2::ll2) ->
      if (Name.compare (label_name l1) (label_name l2) < 0) then
        let%bind (ds1,ds2) = unify_labels ll1 ls2 in
        return (ds1, l1::ds2)
      else if (Name.compare (label_name l1) (label_name l2) > 0) then
        let%bind (ds1,ds2) = unify_labels ls1 ll2 in
        return (l2::ds1, ds2)
      else
        unify l1 l2 >>
        let%bind ll1' = (get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> ll1)) in
        let%bind ll2' = (get_subst >>= fun (sub) -> return TypeVar.HasTypeVar_list_typ.(sub |-> ll2)) in
        unify_labels ll1 ll2

and unify_pred (p1:pred) (p2:pred) : unit UnifyM.t = let open UnifyM in
  match p1, p2 with
  | PredSub(t1,t2), PredSub(u1,u2) ->
      unify t1 u1 >>
      let%bind st2 = subst t2 in
      let%bind su2 = subst u2 in
      unify st2 su2
  | PredIFace(name1,ts1), PredIFace(name2, ts2)
    when Name.equal name1 name2 ->
      unifies ts1 ts2
  | _,_ -> error NoMatchPred

(* unify predicates (applies a substitution before each unification) *)
and unify_preds ps1 ps2 = let open UnifyM in
  match ps1,ps2 with
  | [],[] -> return ()
  | p1::ps1, p2::ps2 ->
      let%bind sp1 = subst_pred p1 in 
      let%bind sp2 = subst_pred p2 in
      unify_pred p1 p2 >>
      unify_preds ps1 ps2
  | _,_ -> failwith "Type.Unify.unify_preds"

(**
 * @entails skolems known preds@ returns both predicates that need to be proved
 * and a core transformer that applies the evidence for @preds@ and abstracts for
 * those in @known@. The @preds@ are entailed by
 * @known@ and predicates containing a type variable in @skolems@ must be entailed
 * completely by other predicates (not containing such skolems). *)
let rec entails (skolems:TypeVar.Set.t) (known:evidence list) = function
  | [] -> UnifyM.return ([],id)
  (* TODO: possible failure point here *)
  | evs when List.equal ~equal:Eq_pred.equal
               (List.map ~f:(fun e -> e.ev_pred) known)
               (List.map ~f:(fun e -> e.ev_pred) evs) ->
      UnifyM.return (evs,id)
  | ev::evs -> match ev.ev_pred with
    | PredIFace(name,[_;_;_]) when name = Name.pred_heap_div -> (* can always be solved *)
        entails skolems known evs
    | _ -> UnifyM.error NoEntail
             
(**
 * `subsume free t_1 t_2` holds if $t_2$ can be instantiated to $t_1$ where
 * `free` are the free type variables in the assumptnio. Returns under
 * which predicates this holds and a core transformer that needs to be applied
 * to the expressions of type $t_2$. Also returns a new type for the expect type 
 * $t_1$ where 'some' types have been properly substitude (and may be quantified) *)
let subsume (free:TypeVar.Set.t) (tp1:typ) (tp2:typ)
  : (typ * evidence list * (Heart.Expr.expr -> Heart.Expr.expr)) UnifyM.t = let open UnifyM in
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
            Heart.Expr.add_type_lambdas vars @@                                   (* generalize *)
            TypeVar.HasTypeVar_expr.(subx |-> (core_ent @@                     (* apply evidence evs2 & abstract evidence evs1 *)
                                               Heart.Expr.add_type_apps tvs expr))) (* instantiate *)
    

(** Does a function type match the given arguments? If the first argument 'matchSome' is true,
 ** it is considered a match even if not all arguments to the function are supplied. *)
let match_arguments (match_some:bool) (* (range:range) *) (free:TypeVar.Set.t) (tp:typ) (fixed:typ list) (named:(Name.t * typ) list) : unit UnifyM.t =
  let open UnifyM in 
  let rho1 = instantiate tp in
  match split_fun_type rho1 with
  | None -> error NoMatch
  | Some(pars,_,_) ->
      if (List.length fixed) + (List.length named) > List.length pars then
        error NoMatch
      else                      (* subsume fixed parameters *)
        let (fpars, npars) = List.split_n pars (List.length fixed) in
        mapM (fun (tpar,targ) -> subsume free (unoptional tpar) targ) (List.zip_exn (List.map ~f:snd fpars) fixed) >>
        (* subsume named parameters *)
        mapM (fun (name,targ) -> match List.Assoc.find npars name ~equal:Name.equal with
            | None -> error NoMatch
            | Some tpar -> subsume free tpar (make_optional targ)) named >>

        (* check the rest is optional *)
        let rest =
          let names = (List.map ~f:fst named) in
          lazy List.(npars >>= fun (nm,tpar) ->
                     guard @@ not (List.mem names nm ~equal:Name.equal) >>= fun _ ->
                     return tpar)
        in
        if match_some || List.for_all ~f:is_optional (Lazy.force rest) then
          return ()
        else
          error NoMatch
