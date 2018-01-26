open Core
open Common
open Common.Util


type t = Heart.Type.type_var
let compare = Heart.Type.compare_type_var
let compare_type_var = Heart.Type.compare_type_var
let to_string = Heart.Type.Show_type_var.show
(* let pp = Type.pp_type_var *)
let sexp_of_t n =
  let open Heart.Type in
  let open Sexplib in
  let sp = sexp_of_pair in
  let ss = sexp_of_string in
  sexp_of_list Fn.id ([
      sp ss Id.sexp_of_t ("type_var_id", n.type_var_id);
      sp ss Heart.Kind.sexp_of_t ("type_var_kind", n.type_var_kind);
      sp ss Flavour.sexp_of_t ("type_var_flavor", n.type_var_flavour)
    ])

let t_of_sexp s =
  let open Heart.Type in
  let open Sexplib in
  let ps = pair_of_sexp in
  let ss = string_of_sexp in
  let a = array_of_sexp Fn.id s in
  {
    type_var_id      = snd (ps ss Id.t_of_sexp a.(0));
    type_var_kind    = snd (ps ss Heart.Kind.t_of_sexp a.(1));
    type_var_flavour = snd (ps ss Flavour.t_of_sexp a.(2));
  }

module C = Comparator.Make(struct
    type nonrec t = t
    let compare = compare
    let sexp_of_t = sexp_of_t
  end)

module Set = Core.Set.Make_using_comparator(struct
    include C
    type nonrec t = t
    let t_of_sexp = t_of_sexp
    let sexp_of_t = sexp_of_t
  end)

module Map = struct
  include Core.Map.Make_using_comparator(struct
      include C
      type nonrec t = t
      let t_of_sexp = t_of_sexp
      let sexp_of_t = sexp_of_t
    end)


  let inter_with ~f m1 m2 =
    fold m1 ~init:empty ~f:(fun ~key ~data acc ->
        match find m2 key with
        | Some data2 -> set acc ~key:key ~data:(f data data2)
        | None -> acc
      )

  (* I've only seen inter_with used with lists, so this is a better
   * version that only cons and doesn't have to do Map.to_alist *)
  let inter_with_to_alist ~f m1 m2 =
    fold m1 ~init:[] ~f:(fun ~key ~data acc ->
        match find m2 key with
        | Some data2 -> (key, f data data2)::acc
        | None -> acc
      )

  (* left-biased union(s) *)
  let union m1 m2 =
    merge m1 m2 ~f:(fun ~key -> function `Both(l,r) -> Some l | `Left l -> Some l | `Right r -> Some r)

  let rec union_list = function
    | [] -> empty
    | x::[] -> x
    | x::ys -> union x (union_list ys)
end


(********************************************************************
 * Debugging
 ********************************************************************)
let show_type_var { Heart.Type.type_var_id=name ; Heart.Type.type_var_kind=kind; _} =
  Id.show name ^ " : " ^ Heart.Kind.show kind

let rec show_tp =
  let open Heart.Type in function
    | Heart.Type.TVar tvar -> show_type_var tvar
    | Heart.Type.TCon tcon -> Name.show tcon.type_con_name ^ " : " ^ Heart.Kind.show tcon.type_con_kind
    | TApp(tp,args)  -> show_tp tp ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">"
    | TSyn(syn,args,body) -> "(syn:" ^ Name.show syn.type_syn_name ^ " : " ^ Heart.Kind.show syn.type_syn_kind
                             ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">" ^ "[" ^ show_tp body ^ "])"
    | _ -> "?"

(**********************************************************************
 * Type variables
 **********************************************************************)

let tvs_empty = Set.empty
let tvs_is_empty = Set.is_empty
let tvs_single = Set.singleton
let tvs_insert = Fn.flip Set.add
let tvs_insert_all vars s = List.fold ~init:s ~f:Set.add vars
let tvs_new = Set.of_list
let tvs_list = Set.to_list
let tvs_remove tvs set = List.fold tvs ~init:set ~f:Set.remove
let tvs_diff = Set.diff
let tvs_union = Set.union
let tvs_unions tvs = List.fold tvs ~init:tvs_empty ~f:Set.union
let tvs_filter = Set.filter
let tvs_member = Set.mem
let tvs_interset = Set.inter
let tvs_disjoint = Set.is_empty <.:> Set.inter
let tvs_common t1 t2 = not @@ Set.is_empty @@ Set.inter t1 t2
let tvs_is_subset_of t1 t2 = Set.is_subset t1 ~of_:t2 (* Is first argument a subset of second? *)


(***************************************************************************
   Substitution

   A substitution can be seen as a mapping from one domain to another, and
   is usually denoted by $\sigma :V \mapsto T$ for some given variable $V$ and term $T$.
   In type variables, this is no different, and can be noted as
   $\sigma : \alpha \mapsto \tau$, where $\alpha$ is a type variable, and $\tau$ is
   some type, which could be a type variable itself.

   Because of this mapping, substitutions can be composed much like functions.
   Given $s1 = \alpha \mapsto \beta$ and of $s2 = \beta \mapsto \gamma$
   the composition $(s1 \circ s2) \mapsto x$ must be the same as $s1 \mapsto (s2 \mapsto x)$
   
   Since there's no \circ operator in code, here we're going to use `@@@`. In
   the original Haskell, `@@` was used. But because `@@` is a primitive operator
   in OCaml, we won't use that.


   Daan's notes:
   For a substitution it should hold that:
   $(s1 \circ s2) \mapsto x  \Leftrightarrow  s1 \mapsto (s2 \mapsto x)$


   We can implement this by:
   1) upon encountering a composition we apply the first substitution
     to the other, and finding an identifier is a simple lookup.
   or,
   2) we compose by simple union and perform a fixpoint at lookup.

   We have chosen (1) here, but it could be interesting to compare
   performance with strategy (2).
 ***************************************************************************)
type tau = Heart.Type.tau       (* $\tau$ *)
type sub = tau Map.t            (* \sigma:\alpha \mapsto \tau *)

(**********************************************************************
 * Entities with type variables
 **********************************************************************)

(* Entities that contain type variables *)
module type HasTypeVar = sig
  type t
  (* Substitute type variables by $\tau$ types *)
  val substitute : sub -> t -> t
  (* Return free type variables *)
  val ftv : t -> Set.t
  (* Return bound type variables *)
  val btv : t -> Set.t
end

module type HasTypeVarEx = sig
  include HasTypeVar
  val (|->) : sub -> t -> t
end

(* Entities that contain type variables that can be put in a particular order *)
module type HasOrderedTypeVar = sig
  type t
  (* Return free type variables in a particular order, may contain duplicates *)
  val odftv : t -> Heart.Type.type_var list
end


(* TODO: inline-replace all of these with their corresponding functions *)

let sub_count : sub -> int = Map.length
let sub_null : sub = Map.empty
let sub_is_null : sub -> bool = Map.is_empty
let sub_new (sub : (t * tau) list) : sub =
  Failure.assertwith (Printf.sprintf "TypeVar.sub_new.KindMisMatch: %i {%s}" (List.length sub)
                        (String.concat @@ List.map ~f:(fun (x,t) -> Printf.sprintf "(%s |-> %s)" (show_type_var x) (show_tp t)) sub))
    (List.for_all ~f:(fun (x,t) -> Heart.Kind.equal (TypeKind.get_kind_type_var x) (TypeKind.get_kind_typ t)) sub)
    Map.of_alist_exn sub          (* TODO: Don't let this throw an exception *)

(** This is the set of all types in our current environment.
 * In type theory, it is denoted by $\Gamma$ *)
let sub_dom : sub -> Set.t = tvs_new <.> Map.keys
let sub_range : sub -> tau list = Map.data
let sub_list : sub -> (Heart.Type.type_var * tau) list = Map.to_alist
let sub_common : sub -> sub -> (t*(tau*tau)) list =
  Map.inter_with_to_alist ~f:Tuple2.create

let sub_lookup tvar sub : tau option = Map.find sub tvar
let sub_remove tvars sub : sub = List.fold tvars ~f:Map.remove ~init:sub
let sub_find tvar sub : tau = match sub_lookup tvar sub with
  | None -> Heart.Type.TVar tvar
  | Some tau ->
      Failure.assertwith ("Type.TypeVar.sub_find: incompatible kind: "
                          ^ Heart.Type.Show_type_var.show tvar ^ ":"
                          ^ Heart.Kind.show (TypeKind.get_kind_type_var tvar) ^ ","
                          ^ "?" ^ ":" ^ Heart.Kind.show (TypeKind.get_kind_typ tau))
        (Heart.Kind.equal (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau)) @@
      tau

module HasTypeVar_list (H:HasTypeVar) : HasTypeVarEx with type t = H.t list = struct
  type t = H.t list
  let substitute sub xs = List.map xs ~f:(fun x -> H.substitute sub x)
  let ftv xs = tvs_unions (List.map xs ~f:H.ftv)
  let btv xs = tvs_unions (List.map xs ~f:H.btv)
  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end

module HasOrderedTypeVar_list (H:HasOrderedTypeVar) : HasOrderedTypeVar with type t = H.t list = struct
  type t = H.t list
  let odftv xs = List.concat_map ~f:H.odftv xs
end   

module rec HasTypeVar_pred : HasTypeVarEx with type t = Heart.Type.pred = struct
  open Heart.Type
  
  type t = pred

  let substitute subst pred = match pred with
    | PredSub (sub, super) -> PredSub (HasTypeVar_typ.substitute subst sub,
                                       HasTypeVar_typ.substitute subst super)
    | PredIFace (name, args) -> PredIFace (name, HasTypeVar_list_typ.substitute subst args)

  let ftv = function
    | PredSub (sub, super) -> tvs_union (HasTypeVar_typ.ftv sub) (HasTypeVar_typ.ftv super)
    | PredIFace (_, args) -> HasTypeVar_list_typ.ftv args
  let btv _ = tvs_empty
  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end

and HasTypeVar_typ : HasTypeVarEx with type t = Heart.Type.typ = struct
  open Heart.Type
  type t = typ
  let substitute (sub:sub) (t:rho) =
    let rec substitute' sub t =
      match t with
      | TForall (vars,preds,tp) ->
          let sub' = sub_remove vars sub in
          let (|->) sub x = if sub_is_null sub then x else HasTypeVar_list_pred.substitute sub x in
          TForall (vars, (sub' |-> preds), (if sub_is_null sub' then tp else substitute' sub' tp))

      | TFun (args,effect,result) ->
          let mapped_args = List.map ~f:(fun (name,tp) -> (name, substitute' sub tp)) args in
          Heart.Type.TFun (mapped_args, (substitute' sub effect), (substitute' sub result))
      | TCon _ -> t
      | TVar tvar -> sub_find tvar sub
      | TApp (tp,arg) ->
          Heart.Type.TApp (substitute' sub tp, HasTypeVar_list_typ.substitute sub arg)
      | TSyn (syn,xs,tp) ->
          TSyn (syn, HasTypeVar_list_typ.substitute sub xs, substitute' sub tp)
    in substitute' sub t

  let ftv tp =
    let rec ftv' = function
      | TForall (vars, preds, tp) ->
          tvs_remove vars (tvs_union (HasTypeVar_list_pred.ftv preds) (ftv' tp))
      | TFun (args, effect, result) ->
          tvs_unions (ftv' effect :: ftv' result :: List.map ~f:(ftv' <.> snd) args)
      | TCon _ -> tvs_empty
      | TVar tvar -> tvs_single tvar
      | TApp (tp, args) -> tvs_union (ftv' tp) (HasTypeVar_list_typ.ftv args)
      | TSyn (syn, xs, tp) -> tvs_union (HasTypeVar_list_typ.ftv xs) (ftv' tp)
    in ftv' tp

  let btv tp =
    let rec btv' = function
      | TForall (vars, preds, tp) -> tvs_remove vars (tvs_union (HasTypeVar_list_pred.ftv preds) (btv' tp))
      | TFun (args, effect, result) -> tvs_unions (btv' effect :: btv' result :: List.map ~f:(btv' <.> snd) args)
      | TSyn (_,_,tp) -> btv' tp
      | TApp (tp, args) -> tvs_union (btv' tp) (HasTypeVar_list_typ.btv args)
      | _ -> tvs_empty
    in btv' tp

  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end

and HasTypeVar_list_typ : HasTypeVarEx with type t = Heart.Type.typ list = HasTypeVar_list(HasTypeVar_typ)
and HasTypeVar_list_pred : HasTypeVarEx with type t = Heart.Type.pred list = HasTypeVar_list(HasTypeVar_pred)

module rec HasOrderedTypeVar_typ : HasOrderedTypeVar with type t = Heart.Type.typ = struct
  open Heart.Type
  type t = typ
  let odftv tp =
    let rec odftv' = function
      | TForall (vars, preds, tp) ->
          let module HOTV_list_pred = HasOrderedTypeVar_list(HasOrderedTypeVar_pred) in
          List.filter ~f:(fun tv -> not (List.mem vars tv ~equal:Heart.Type.eq_type_var)) (odftv' tp @ HOTV_list_pred.odftv preds)
      | TFun (args, effect, result) ->
          List.concat_map ~f:odftv' ((List.map ~f:snd args) @ [effect; result])
      | TCon _ -> []
      | TVar tvar -> [tvar]
      | TApp (tp, args) ->
          let module HOTV_list_typ = HasOrderedTypeVar_list(HasOrderedTypeVar_typ) in
          (odftv' tp) @ (HOTV_list_typ.odftv args)
      | TSyn (_, xs, tp) -> (odftv' tp) @ (List.concat_map ~f:odftv' xs)
    in odftv' tp
end
and HasOrderedTypeVar_pred : HasOrderedTypeVar with type t = Heart.Type.pred = struct
  type t = Heart.Type.pred
  let odftv tp = assert false
end 

module HasTypeVar_sub = struct
  type t = sub
  let substitute sub (s:sub) = Map.map s ~f:(fun (k:tau) -> HasTypeVar_typ.substitute sub k)
  let ftv sub = tvs_empty (* TODO: tvs_union (tvs_new (Map.keys sub)) (ftv (Map.elems sub)) *)
  let btv _ = tvs_empty
  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end


module HasTypeVar_option(H:HasTypeVar) : HasTypeVar with type t = H.t option = struct
  type t = H.t option
  let substitute sub = function Some x -> Some (H.substitute sub x)
                              | None -> None
  let ftv = function Some x -> H.ftv x
                   | None -> tvs_empty

  let btv = function Some x -> H.btv x
                   | None -> tvs_empty
end

let sub_single tvar (tau:tau) : sub =
  (** Top assertion is invalid; it can happen (and happens) in the CoreF typechecker when
   * typechecking $\forall \alpha. f \alpha$ with $f :: \forall \beta. \beta \rightarrow \beta$, that a bound variable ($\beta$) with
   * number ID must be substituted for another bound variable ($\alpha$), which *could* have the same
   * ID. If we want to avoid this, we must ensure that all IDs are distinct; in particular,
   * the IDs of built-in types such as .select must be distinct from further IDs generated
   * by the compiler. *)
  Map.singleton tvar tau
  |> Failure.assertwith "Type.TypeVar.sub_single.KindMismatch" (Heart.Kind.equal (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau))
  |> Failure.assertwith ("Type.TypeVar.sub_single: recursive type: " ^ show_type_var tvar) (not (Set.mem (HasTypeVar_typ.ftv tau) tvar))

let sub_compose (sub1:sub) (sub2:sub) : sub =
  let open HasTypeVar_sub in
  Map.union sub1 (sub1 |-> sub2)

let (@@@) sub1 sub2 = sub_compose sub1 sub2

let sub_extend (tvar:Heart.Type.type_var) (tau:tau) (sub:sub) =
  (sub_single tvar tau) @@@ sub

let fresh_type_var kind (flavour : Heart.Type.Flavour.t) =
  let open Heart.Kind in
  let id = Unique.unique_id (match flavour with Flavour.Meta -> "_v" | Flavour.Skolem -> "$v" | Flavour.Bound -> "v") in
  Heart.Type.({ type_var_id = id; type_var_kind = kind; type_var_flavour = flavour })


(*********************************************************************
 * HasTypeVar Monad Stuff 
 *********************************************************************)

module HasTypeVar_tname = struct
  type t = Heart.Expr.tname
  let substitute sub (name, tp) = (name, HasTypeVar_typ.substitute sub tp)
  let ftv (name, tp) = HasTypeVar_typ.ftv tp
  let btv (name, tp) = HasTypeVar_typ.btv tp
end

module HasTypeVar_list_tname = HasTypeVar_list(HasTypeVar_tname)

module rec HasTypeVar_def : HasTypeVar with type t = Heart.Expr.def = struct
  open Heart.Expr
  type t = def
  let substitute sub (def:def) = {def with def_type=HasTypeVar_typ.substitute sub def.def_type;
                                           def_expr=HasTypeVar_expr.substitute sub def.def_expr}
  let ftv def = tvs_union (HasTypeVar_typ.ftv def.def_type) (HasTypeVar_expr.ftv def.def_expr)
  let btv def = tvs_union (HasTypeVar_typ.btv def.def_type) (HasTypeVar_expr.btv def.def_expr)
end

and HasTypeVar_list_def : HasTypeVarEx with type t = Heart.Expr.def list
  = HasTypeVar_list(HasTypeVar_def)

and HasTypeVar_defgroup : HasTypeVar = struct
  open Heart.Expr
  type t = def_group
  let substitute sub = function
    | DefRec(defs)   -> DefRec(HasTypeVar_list_def.substitute sub defs)
    | DefNonRec(def) -> DefNonRec(HasTypeVar_def.substitute sub def)
  let ftv = function
    | DefRec(defs)   -> HasTypeVar_list_def.ftv defs
    | DefNonRec(def) -> HasTypeVar_def.ftv def
  let btv = function
    | DefRec(defs)   -> HasTypeVar_list_def.btv defs
    | DefNonRec(def) -> HasTypeVar_def.btv def
end

and HasTypeVar_list_defgroup : HasTypeVarEx with type t = Heart.Expr.def_group list
  = HasTypeVar_list(HasTypeVar_defgroup)

and HasTypeVar_pattern : HasTypeVar with type t = Heart.Expr.pattern = struct
  open Heart.Expr
  type t = pattern
  let rec substitute sub = function
    | PatVariable pvar -> PatVariable{pat_name = HasTypeVar_tname.substitute sub pvar.pat_name;
                                      pat_pattern = substitute sub pvar.pat_pattern}
    | PatConstructor con -> PatConstructor{con with pat_con_name = HasTypeVar_tname.substitute sub con.pat_con_name;
                                                    pat_con_patterns = HasTypeVar_list_pattern.substitute sub con.pat_con_patterns;
                                                    pat_type_args = HasTypeVar_list_typ.substitute sub con.pat_type_args;
                                                    pat_type_res = HasTypeVar_typ.substitute sub con.pat_type_res}
    | PatWild -> PatWild
    | PatLiteral lit -> PatLiteral lit

  let rec ftv = function
    | PatVariable pvar -> tvs_union (HasTypeVar_tname.ftv pvar.pat_name) (ftv pvar.pat_pattern)
    | PatConstructor con -> tvs_unions [HasTypeVar_tname.ftv con.pat_con_name;
                                                HasTypeVar_list_pattern.ftv con.pat_con_patterns;
                                                HasTypeVar_list_typ.ftv con.pat_type_args;
                                                HasTypeVar_typ.ftv con.pat_type_res]
    | PatWild -> tvs_empty
    | PatLiteral _ -> tvs_empty

  let rec btv = function
    | PatVariable pvar -> tvs_union (HasTypeVar_tname.btv pvar.pat_name) (btv pvar.pat_pattern)
    | PatConstructor con -> tvs_unions [HasTypeVar_tname.btv con.pat_con_name;
                                                HasTypeVar_list_pattern.btv con.pat_con_patterns;
                                                HasTypeVar_list_typ.btv con.pat_type_args;
                                                HasTypeVar_typ.btv con.pat_type_res]
    | PatWild -> tvs_empty
    | PatLiteral _ -> tvs_empty
end 

and HasTypeVar_list_pattern : HasTypeVarEx with type t = Heart.Expr.pattern list
  = HasTypeVar_list(HasTypeVar_pattern)

and HasTypeVar_guard : HasTypeVar with type t = Heart.Expr.guard = struct
  open Heart.Expr
  type t = guard
  let substitute sub {guard_test; guard_expr} = {guard_test=HasTypeVar_expr.substitute sub guard_test;
                                                 guard_expr=HasTypeVar_expr.substitute sub guard_expr;}
  let ftv {guard_test; guard_expr} = tvs_union (HasTypeVar_expr.ftv guard_test) (HasTypeVar_expr.ftv guard_expr)
  let btv {guard_test; guard_expr} = tvs_union (HasTypeVar_expr.btv guard_test) (HasTypeVar_expr.btv guard_expr)
end

and HasTypeVar_list_guard : HasTypeVarEx with type t = Heart.Expr.guard list
  = HasTypeVar_list(HasTypeVar_guard)

and HasTypeVar_branch : HasTypeVar with type t = Heart.Expr.branch = struct
  open Heart.Expr
  type t = branch
  let substitute sub {branch_patterns=patterns; branch_guards=guards} =
    let sub' = sub_remove (tvs_list @@ HasTypeVar_list_pattern.btv patterns) sub in
    { branch_patterns=List.map ~f:(HasTypeVar_pattern.substitute sub) patterns;
      branch_guards=List.map ~f:(HasTypeVar_guard.substitute sub') guards }

  let ftv {branch_patterns; branch_guards} =
    tvs_union
      (HasTypeVar_list_pattern.ftv branch_patterns)
      (tvs_diff
         (HasTypeVar_list_guard.ftv branch_guards)
         (HasTypeVar_list_pattern.btv branch_patterns))

  let btv {branch_patterns; branch_guards} =
    tvs_union (HasTypeVar_list_pattern.btv branch_patterns) (HasTypeVar_list_guard.btv branch_guards)
end

and HasTypeVar_list_branch : HasTypeVarEx with type t = Heart.Expr.branch list
  = HasTypeVar_list(HasTypeVar_branch)

and HasTypeVar_expr : HasTypeVarEx with type t = Heart.Expr.expr = struct
  open Heart.Expr
  type t = expr
  let rec substitute sub = function
    | Lam(tnames, eff, expr) -> Lam (HasTypeVar_list_tname.substitute sub tnames,
                                     HasTypeVar_typ.substitute sub eff,
                                     substitute sub expr)
    | Var{var_name=tname; var_info=info} -> Var{var_name=HasTypeVar_tname.substitute sub tname; var_info=info}
    | App(f, args) -> App(substitute sub f, HasTypeVar_list_expr.substitute sub args)
    | TypeLam(tvs, expr) ->
        let sub' = sub_remove tvs sub in
        TypeLam(tvs, HasTypeVar_expr.(sub' |-> expr))
    | TypeApp(expr, tps) -> TypeApp(substitute sub expr, HasTypeVar_list_typ.substitute sub tps)
    | Constructor{con_name=tname; con_repr=repr} -> Constructor{con_name=HasTypeVar_tname.substitute sub tname; con_repr=repr}
    | Literal lit -> Literal lit
    | Let(defgroups, expr) -> Let(HasTypeVar_list_defgroup.substitute sub defgroups, substitute sub expr)
    | Case c -> Case{case_exprs = HasTypeVar_list_expr.substitute sub c.case_exprs;
                     case_branches = HasTypeVar_list_branch.substitute sub c.case_branches}

  let rec ftv = function
    | Lam(tnames, eff, expr) -> tvs_unions [HasTypeVar_list_tname.ftv tnames;
                                                    HasTypeVar_typ.ftv eff;
                                                    ftv expr]
    | Var v -> HasTypeVar_tname.ftv v.var_name
    | App(f, args) -> tvs_union (ftv f) (HasTypeVar_list_expr.ftv args)
    | TypeLam(tvs, expr) -> tvs_remove tvs (ftv expr)
    | TypeApp(expr, tps) -> tvs_union (ftv expr) (HasTypeVar_list_typ.ftv tps)
    | Constructor c -> HasTypeVar_tname.ftv c.con_name
    | Literal _ -> tvs_empty
    | Let(defgroups, expr) -> tvs_union (HasTypeVar_list_defgroup.ftv defgroups) (ftv expr)
    | Case c -> tvs_union (HasTypeVar_list_expr.ftv c.case_exprs) (HasTypeVar_list_branch.ftv c.case_branches)

  let rec btv = function
    | Lam(tnames, eff, expr) -> tvs_unions [HasTypeVar_list_tname.btv tnames;
                                                    HasTypeVar_typ.btv eff;
                                                    btv expr]
    | Var v -> HasTypeVar_tname.btv v.var_name
    | App(f, args) -> tvs_union (btv f) (HasTypeVar_list_expr.btv args)
    | TypeLam(tvs, expr) -> tvs_insert_all tvs (btv expr) (* The magic *)
    | TypeApp(expr, tps) -> tvs_union (btv expr) (HasTypeVar_list_typ.btv tps)
    | Constructor c -> HasTypeVar_tname.btv c.con_name
    | Literal _ -> tvs_empty
    | Let(defgroups, expr) -> tvs_union (HasTypeVar_list_defgroup.btv defgroups) (btv expr)
    | Case c -> tvs_union (HasTypeVar_list_expr.btv c.case_exprs) (HasTypeVar_list_branch.btv c.case_branches)

  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end
and HasTypeVar_list_expr : HasTypeVarEx with type t = Heart.Expr.expr list = HasTypeVar_list(HasTypeVar_expr)
