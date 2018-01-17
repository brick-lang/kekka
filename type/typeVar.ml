open Core                       (* TODO: Make this Core_kernel
                                 * and turn TVMap and TVSet into
                                 * Map and Set*)
open Type
open Kind
open Common
open Common.Util

(* Really fancy module magic *)
module T = struct
  type t = Type.type_var
  let compare = Type.compare_type_var
  let compare_type_var = Type.compare_type_var
  let to_string = Type.Show_type_var.show
  (* let pp = Type.pp_type_var *)
  let sexp_of_t n =
    let open Type in
    let open Sexplib in
    let sp = sexp_of_pair in
    let ss = sexp_of_string in
    sexp_of_list Fn.id ([
        sp ss Id.sexp_of_id ("type_var_id", n.type_var_id);
        sp ss Kind.sexp_of_kind ("type_var_kind", n.type_var_kind);
        sp ss sexp_of_flavour ("type_var_flavor", n.type_var_flavour)
      ])

  let t_of_sexp s =
    let open Type in
    let open Sexplib in
    let ps = pair_of_sexp in
    let ss = string_of_sexp in
    let a = array_of_sexp Fn.id s in
    {
      type_var_id      = snd (ps ss Id.id_of_sexp a.(0));
      type_var_kind    = snd (ps ss Kind.kind_of_sexp a.(1));
      type_var_flavour = snd (ps ss flavour_of_sexp a.(2));
    }
end
include T

module C = Comparable.Make(T)
(* include C *)

module TVSet = Core.Set.Make_using_comparator(struct
    include T
    include C
  end)

module TVMap = struct
  include Core.Map.Make_using_comparator(struct
      include T
      include C
    end)

  let inter_with ~f m1 m2 =
    fold m1 ~init:empty ~f:(fun ~key ~data acc ->
        match find m2 key with
        | Some data2 -> add acc ~key:key ~data:(f data data2)
        | None -> acc
      )

  (* I've only seen inter_with used with lists, so this is a better
   * version that only cons and doesn't have to do TVMap.to_alist *)
  let inter_with_to_alist ~f m1 m2 =
    fold m1 ~init:[] ~f:(fun ~key ~data acc ->
        match find m2 key with
        | Some data2 -> (key, f data data2)::acc
        | None -> acc
      )

  (* Left-biased union *)
  let union m1 m2 =
    let m1_vals = to_alist m1 in
    List.fold_left m1_vals ~f:(fun m (k,v) -> add m ~key:k ~data:v) ~init:m2

  let elems m1 =
    let m1_pairs = to_alist m1 in
    List.map m1_pairs ~f:(fun (k,v) -> v)
end


(********************************************************************
 * Debugging
 ********************************************************************)
let show_type_var { Type.type_var_id=name ; Type.type_var_kind=kind; _} =
  Id.show_id name ^ " : " ^ Kind.Show_kind.show kind

let rec show_tp =
  let open Type in function
    | Type.TVar tvar -> show_type_var tvar
    | Type.TCon tcon -> Name.show_name tcon.type_con_name ^ " : " ^ Show_kind.show tcon.type_con_kind
    | TApp(tp,args)  -> show_tp tp ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">"
    | TSyn(syn,args,body) -> "(syn:" ^ Name.show_name syn.type_syn_name ^ " : " ^ Show_kind.show syn.type_syn_kind
                             ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">" ^ "[" ^ show_tp body ^ "])"
    | _ -> "?"

(**********************************************************************
 * Type variables
 **********************************************************************)

let tvs_empty = TVSet.empty
let tvs_is_empty = TVSet.is_empty
let tvs_single = TVSet.singleton
let tvs_insert = Fn.flip TVSet.add
let tvs_insert_all vars s = List.fold ~init:s ~f:TVSet.add vars
let tvs_new = TVSet.of_list
let tvs_list = TVSet.to_list
let tvs_remove tvs set = List.fold tvs ~init:set ~f:TVSet.remove
let tvs_diff = TVSet.diff
let tvs_union = TVSet.union
let tvs_unions tvs = List.fold tvs ~init:tvs_empty ~f:TVSet.union
let tvs_filter = TVSet.filter
let tvs_member = TVSet.mem
let tvs_interset = TVSet.inter
let tvs_disjoint = TVSet.is_empty <.:> TVSet.inter
let tvs_common t1 t2 = not @@ TVSet.is_empty @@ TVSet.inter t1 t2
let tvs_is_subset_of t1 t2 = TVSet.is_subset t1 ~of_:t2 (* Is first argument a subset of second? *)


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
type tau = Type.tau             (* $\tau$ *)
type sub = tau TVMap.t          (* \sigma:\alpha \mapsto \tau *)

(**********************************************************************
 * Entities with type variables
 **********************************************************************)

(* Entities that contain type variables *)
module type HasTypeVar = sig
  type t
  (* Substitute type variables by $\tau$ types *)
  val substitute : sub -> t -> t
  (* Return free type variables *)
  val ftv : t -> TVSet.t
  (* Return bound type variables *)
  val btv : t -> TVSet.t
end

module type HasTypeVarEx = sig
  include HasTypeVar
  val (|->) : sub -> t -> t
end

(* Entities that contain type variables that can be put in a particular order *)
module type HasOrderedTypeVar = sig
  type t
  (* Return free type variables in a particular order, may contain duplicates *)
  val odftv : t -> type_var list
end


(* TODO: inline-replace all of these with their corresponding functions *)

let sub_count : sub -> int = TVMap.length
let sub_null : sub = TVMap.empty
let sub_is_null : sub -> bool = TVMap.is_empty
let sub_new (sub : (t * tau) list) : sub =
  Failure.assertion ("TypeVar.sub_new.KindMisMatch: " ^ (string_of_int @@ List.length sub)
                     ^ String.concat (List.map ~f:(fun (x,t) -> "(" ^ show_type_var x ^ " |-> " ^ show_tp t ^ ")") sub))
    (List.for_all ~f:(fun (x,t) -> Eq_kind.equal (TypeKind.get_kind_type_var x) (TypeKind.get_kind_typ t)) sub)
    C.Map.of_alist_exn sub          (* TODO: Don't let this throw an exception *)

(** This is the set of all types in our current environment.
 * In type theory, it is denoted by $\Gamma$ *)
let sub_dom : sub -> TVSet.t = tvs_new <.> TVMap.keys
let sub_range : sub -> tau list = TVMap.data
let sub_list : sub -> (type_var * tau) list = TVMap.to_alist
let sub_common : sub -> sub -> (t*(tau*tau)) list =
  TVMap.inter_with_to_alist ~f:Tuple2.create

let sub_lookup tvar sub : tau option = TVMap.find sub tvar
let sub_remove tvars sub : sub = List.fold tvars ~f:TVMap.remove ~init:sub
let sub_find tvar sub : tau = match sub_lookup tvar sub with
  | None -> Type.TVar tvar
  | Some tau ->
      Failure.assertion ("Type.TypeVar.sub_find: incompatible kind: "
                         ^ Show_type_var.show tvar ^ ":"
                         ^ Show_kind.show (TypeKind.get_kind_type_var tvar) ^ ","
                         ^ "?" ^ ":" ^ Show_kind.show (TypeKind.get_kind_typ tau))
        (Eq_kind.equal (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau)) @@
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

module rec HasTypeVar_pred : HasTypeVarEx with type t = pred = struct
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

and HasTypeVar_typ : HasTypeVarEx with type t = typ = struct
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
          Type.TFun (mapped_args, (substitute' sub effect), (substitute' sub result))
      | TCon _ -> t
      | TVar tvar -> sub_find tvar sub
      | TApp (tp,arg) ->
          Type.TApp (substitute' sub tp, HasTypeVar_list_typ.substitute sub arg)
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

and HasTypeVar_list_typ : HasTypeVarEx with type t = typ list = HasTypeVar_list(HasTypeVar_typ)
and HasTypeVar_list_pred : HasTypeVarEx with type t = pred list = HasTypeVar_list(HasTypeVar_pred)

module rec HasOrderedTypeVar_typ : HasOrderedTypeVar with type t = typ = struct
  type t = typ
  let odftv tp =
    let rec odftv' = function
      | TForall (vars, preds, tp) ->
          let module HOTV_list_pred = HasOrderedTypeVar_list(HasOrderedTypeVar_pred) in
          List.filter ~f:(fun tv -> not (List.mem vars tv ~equal:Type.eq_type_var)) (odftv' tp @ HOTV_list_pred.odftv preds)
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
and HasOrderedTypeVar_pred : HasOrderedTypeVar with type t = pred = struct
  type t = pred
  let odftv tp = assert false
end 

module HasTypeVar_sub = struct
  type t = sub
  let substitute sub (s:sub) = TVMap.map s ~f:(fun (k:tau) -> HasTypeVar_typ.substitute sub k)
  let ftv sub = tvs_empty (* TODO: tvs_union (tvs_new (TVMap.keys sub)) (ftv (TVMap.elems sub)) *)
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
  Failure.assertion ("Type.TypeVar.sub_single: recursive type: " ^ show_type_var tvar) (not (TVSet.mem (HasTypeVar_typ.ftv tau) tvar)) @@
  Failure.assertion "Type.TypeVar.sub_single.KindMismatch" (Eq_kind.equal (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau)) @@
  C.Map.singleton tvar tau

let sub_compose (sub1:sub) (sub2:sub) : sub =
  let open HasTypeVar_sub in
  TVMap.union sub1 (sub1 |-> sub2)

let (@@@) sub1 sub2 = sub_compose sub1 sub2

let fresh_type_var kind (flavour : flavour) =
  let id = Unique.unique_id (match flavour with Meta -> "_v" | Skolem -> "$v" | Bound -> "v") in
  { type_var_id = id; type_var_kind = kind; type_var_flavour = flavour }
