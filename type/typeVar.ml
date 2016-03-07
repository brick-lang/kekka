open Core.Std                   (* TODO: Make this Core_kernel
                                 * and turn TVMap and TVSet into
                                 * Map and Set*)
open Util

(* Really fancy module magic *)
module T = struct
  type t = Type.type_var
  let compare = Type.compare_type_var
  let compare_type_var = Type.compare_type_var
  let to_string = Type.pp_type_var
  let pp = Type.pp_type_var
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
include C

module TVSet = Core.Std.Set.Make_using_comparator(struct
    include T
    include C
  end)

module TVMap = struct
  include Core.Std.Map.Make_using_comparator(struct
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
  Debugging
 ********************************************************************)
let show_type_var { Type.type_var_id=name ; Type.type_var_kind=kind; _} =
  Id.show_id name ^ " : " ^ Kind.show_kind kind

let rec show_tp =
  let open Type in function
    | Type.TVar tvar -> show_type_var tvar
    | Type.TCon tcon -> Name.show_name tcon.type_con_name ^ " : " ^ Kind.show_kind tcon.type_con_kind
    | TApp(tp,args)  -> show_tp tp ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">"
    | TSyn(syn,args,body) -> "(syn:" ^ Name.show_name syn.type_syn_name ^ " : " ^ Kind.show_kind syn.type_syn_kind
                             ^ "<" ^ String.concat ~sep:"," (List.map ~f:show_tp args) ^ ">" ^ "[" ^ show_tp body ^ "])"
    | _ -> "?"

(**********************************************************************
  Type variables
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
let tvs_is_subset_of = TVSet.subset (* Is first argument a subset of second? *)


(***************************************************************************
  Substitution
  ******

  A substitution can be seen as a mapping from one domain to another, and
  is usually denoted by $\sigma :V \mapsto T$ for some given variable $V$ and term $T$.
  in type variables, this is no different, and can be noted as
  $\sigma : \alpha \mapsto \tau$, where $\alpha$ is a type variable, and $\tau$ is
  some type, which could be a type variable itself.

  Because of this mapping, substitutions can be composed much like functions.
  Given $s1 = \alpha \mapsto \beta$ and of $s2 = \beta \mapsto \gamma$
  the composition $(s1 \circ s2) \mapsto x$ must be the same as $s1 \mapsto (s2 \mapsto x)$

  Since there's no \circ operator in code, here we're going to use `$`. In
  the original Haskell, `@@` was used. But because `@@` is a primitive operator
  in OCaml, we won't use that. Coincindentally, it's the equivalent of the `$`
  operator in Haskell.


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
  Entities with type variables
 **********************************************************************)

(* Entities that contain type variables *)
module type HasTypeVar = sig
  type a
  (* Substitute type variables by $\tau$ types *)
  val substitute : sub -> a -> a
  (* Return free type variables *)
  val ftv : a -> TVSet.t
  (* Return bound type variables *)
  val btv : a -> TVSet.t
end

(* Entities that contain type variables that can be put in a particular order *)
module type HasOrderedTypeVar = sig
  (* Return free type variables in a particular order, may contain duplicates *)
  val odftv : tau -> t list
end
(* TODO: inline-replace all of these with their corresponding functions *)

let sub_count : sub -> int = TVMap.length
let sub_null : sub = TVMap.empty
let sub_is_null : sub -> bool = TVMap.is_empty
let sub_new (sub : (t * tau) list) : sub =
  Failure.assertion ("TypeVar.sub_new.KindMisMatch: " ^ (string_of_int @@ List.length sub)
                     ^ String.concat (List.map ~f:(fun (x,t) -> "(" ^ show_type_var x ^ " |-> " ^ show_tp t ^ ")") sub))
    (List.for_all ~f:(fun (x,t) -> Kind.equal_kind (TypeKind.get_kind_type_var x) (TypeKind.get_kind_typ t)) sub)
    Map.of_alist_exn sub          (* TODO: Don't let this throw an exception *)

let sub_range : sub -> tau list = TVMap.data


(** This is the set of all types in our current environment.
 * In type theory, it is denoted by $\Gamma$ *)
let sub_dom : sub -> TVSet.t = tvs_new <.> TVMap.keys
let sub_list = TVMap.to_alist
let sub_common : sub -> sub -> (t*(tau*tau)) list =
  TVMap.inter_with_to_alist ~f:Tuple2.create
let sub_lookup tvar sub : tau option = TVMap.find sub tvar
let sub_remove tvars sub : sub = List.fold tvars ~f:TVMap.remove ~init:sub
let sub_find tvar sub : tau = match sub_lookup tvar sub with
  | None -> Type.TVar tvar
  | Some tau ->
      Failure.assertion ("Type.TypeVar.sub_find: incompatible kind: "
                         ^ Type.show_type_var tvar ^ ":"
                         ^ Kind.show_kind (TypeKind.get_kind_type_var tvar) ^ ","
                         ^ "?" ^ ":" ^ Kind.show_kind (TypeKind.get_kind_typ tau))
        (Kind.equal_kind (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau)) @@
      tau



(* GADTs GAHHHH *)
type _ has_type_var =
  | Sub  : tau has_type_var TVMap.t -> tau has_type_var TVMap.t has_type_var
  | Option : 'a has_type_var option -> 'a has_type_var option has_type_var
  | Pair : 'b has_type_var * 'c has_type_var -> ('b has_type_var * 'c has_type_var) has_type_var
  | Type : tau -> tau has_type_var
  | Pred : Type.pred -> Type.pred has_type_var
  | List : 'a has_type_var list -> 'a has_type_var list has_type_var
  (* | Range : range -> range has_type_var *)


let rec ftv : type a. a has_type_var -> TVSet.t = function
  | Sub sub -> tvs_union (tvs_new (TVMap.keys sub))
                 (ftv @@ List (TVMap.elems sub))
  | Option mb -> (match mb with Some x -> ftv x | None -> tvs_empty)
  | Pair (x,y) -> tvs_union (ftv x) (ftv y)
  | List xs -> tvs_unions (List.map ~f:ftv xs)
  (* | Range _ -> tvs_empty *)
  | Type t -> begin
      let open Type in
      match t with
      | TForall (vars,preds,tp) -> tvs_remove vars (tvs_union (ftv @@ List (List.map ~f:(fun x -> Pred x) preds)) (ftv (Type tp)))
      | TFun (args,effect,result) -> tvs_unions (ftv (Type effect) :: ftv (Type result)
                                                 :: List.map ~f:(fun x -> ftv @@ Type (snd x)) args)
      | TCon _ -> tvs_empty
      | TVar tvar -> tvs_single tvar
      | TApp (tp,arg) -> tvs_union (ftv (Type tp)) (ftv @@ List (List.map ~f:(fun x -> Type x) arg))
      | TSyn (syn,xs,tp) -> tvs_union (ftv @@ List (List.map ~f:(fun x -> Type x) xs)) (ftv (Type tp))
    end
  | Pred p -> begin
      match p with
      | Type.PredSub (sub,super) -> tvs_union (ftv (Type sub)) (ftv (Type super))
      | Type.PredIFace (name, args) -> ftv @@ List (List.map ~f:(fun x -> Type x) args)
    end 
    

let rec btv : type a. a has_type_var -> TVSet.t = function
  | Sub sub -> tvs_union (tvs_new (TVMap.keys sub))
                 (ftv @@ List (TVMap.elems sub))
  | Option mb -> (match mb with Some x -> ftv x | None -> tvs_empty)
  | Pair (x,y) -> tvs_union (btv x) (btv y)
  | List xs -> tvs_unions (List.map ~f:btv xs)
  (* | Range _ -> tvs_empty *)
  | Type t -> begin
      let open Type in
      match t with
      | TForall (vars,preds,tp) -> tvs_insert_all vars (tvs_union (ftv @@ List (List.map ~f:(fun x -> Pred x) preds)) (btv (Type tp)))
      | TFun (args,effect,result) -> tvs_unions (btv (Type effect) :: btv (Type result)
                                                 :: List.map ~f:(fun x -> btv @@ Type (snd x)) args)
      | TSyn (syn,xs,tp) -> btv @@ Type tp
      | TApp (tp,arg) -> tvs_union (btv (Type tp)) (btv @@ List (List.map ~f:(fun x -> Type x) arg))
      | _ -> tvs_empty
    end
  | Pred _ -> tvs_empty
  
let unwrap : type a. a has_type_var -> a = function
  | Sub s -> s
  | Type t -> t
  | List l -> l
  | Pred p -> p
  | Option o -> o
  | Pair (x,y) -> (x,y)

let rec substitute : type a. sub -> a has_type_var -> a has_type_var = fun sub -> function
  | Sub s -> Sub (TVMap.map s ~f:(fun k -> substitute sub k))
  | Option mb ->
      (match mb with Some x -> Option (Some (substitute sub x))
                   | None -> Option None)
  | Pair (x,y) -> Pair (substitute sub x, substitute sub y)
  | List xs -> List (List.map ~f:(substitute sub) xs)
  (* | Range r -> r *)
  | Type t -> Type begin
      match t with
      | Type.TForall (vars,preds,tp) ->
          let sub' = sub_remove vars sub in
          let preds = List (List.map preds ~f:(fun p -> Pred p)) in
          Type.TForall (vars,
                              List.map ~f:unwrap @@ unwrap (sub' |-> preds),
                              unwrap (sub' |-> (Type tp)))
      | Type.TFun (args,effect,result) ->
          Type.TFun (List.map ~f:(fun (name,tp) -> (name, unwrap @@ substitute sub (Type tp))) args,
                           unwrap (substitute sub (Type effect)),
                           unwrap (substitute sub (Type result)))
      | Type.TCon _ -> t
      | Type.TVar tvar -> sub_find tvar sub
      | Type.TApp (tp,arg) -> Type.TApp (unwrap @@ substitute sub (Type tp),
                                         (List.map ~f:unwrap @@
                                          unwrap @@ substitute sub (List (List.map ~f:(fun x -> Type x) arg))))
      | Type.TSyn (syn,xs,tp) -> Type.TSyn (syn,
                                            (List.map ~f:unwrap @@
                                             unwrap @@ substitute sub (List (List.map ~f:(fun x -> Type x) xs))),
                                            unwrap @@ substitute sub (Type tp))
    end
  | Pred p -> begin
      match p with
      | Type.PredSub (sub',super) -> Pred (Type.PredSub (unwrap @@ substitute sub (Type sub'),
                                                         unwrap @@ substitute sub (Type super)))
      | Type.PredIFace (name,args) -> Pred (Type.PredIFace (name,
                                                            List.map ~f:unwrap @@
                                                            unwrap @@ substitute sub (List (List.map ~f:(fun x -> Type x) args))))
    end

  (* | Type t -> begin match t with *)
  (*     | Type.TForall (vars,preds,tp) -> *)
  (*         let sub' = sub_remove vars sub in *)
  (*         let preds : Type.pred has_type_var list = List.map preds ~f:(fun p -> Pred p) in *)
  (*         let preds : Type.pred has_type_var list has_type_var = List preds in *)
  (*         Type.TForall (vars, List.map ~f:unwrap (sub' |-> preds), (sub' |-> (Type tp))) *)
  (*   end *)


and (|->) : type a. sub -> a has_type_var -> a has_type_var = fun sub x ->
  if sub_is_null sub then
    x
  else
    (substitute sub x)


let sub_single tvar (tau:tau) : sub =
  (** Top assertion is invalid; it can happen (and happens) in the CoreF typechecker when
   * typechecking $\forall \alpha. f \alpha$ with $f :: \forall \beta. \beta \rightarrow \beta$, that a bound variable ($\beta$) with
   * number ID must be substituted for another bound variable ($\alpha$), which *could* have the same
   * ID. If we want to avoid this, we must ensure that all IDs are distinct; in particular,
   * the IDs of built-in types such as .select must be distinct from further IDs generated
   * by the compiler. *)
  Failure.assertion ("Type.TypeVar.sub_single: recursive type: " ^ show_type_var tvar)
    (not (TVSet.mem (ftv (Type tau)) tvar)) @@
  Failure.assertion "Type.TypeVar.sub_single.KindMismatch" (Kind.equal_kind (TypeKind.get_kind_type_var tvar) (TypeKind.get_kind_typ tau)) @@
  Map.singleton tvar tau

let sub_find tvar sub : tau =
  match sub_lookup tvar sub with
  | None -> Type.TVar tvar
  | Some tau -> Failure.assertion ("Type.TypeVar.sub_find: incompatible kind: "
                                   ^ show_type_var tvar ^ ":"
                                   ^ Kind.show_kind (TypeKind.get_kind_type_var tvar) ^ ","
                                   ^ "?" ^ ":" ^ Kind.show_kind (TypeKind.get_kind_typ tau))
                  (Kind.equal_kind (TypeKind.get_kind_type_var tvar)
                     (TypeKind.get_kind_typ tau)) tau


(* let sub_compose sub1 (sub2:sub) : sub = TVMap.union sub1 (sub1 |-> sub2) *)

(* let (@@@) sub1 sub2 = sub_compose sub1 sub2 *)
