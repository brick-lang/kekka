(**
 * types.ml
 * Ported from Daan Leijin's implementation,
 * which is licensed under the APLv2.0
 * Copyright 2012 Microsoft Corporation, Daan Leijen
 * Copyright 2015 Katherine Whitlock
*)
open Common

(** This is the primary type-system, the heart of $\lambda^k$ *)


(**
 * Type variables are variables in a type and contain an identifier and
 * kind. One can ask for the free type variables in a type, and substitute
 * them with '$\tau$' types.
 * Eg. $\alpha^K$ *)
module TypeVar = struct
  type t = {
    id      : Id.t;
    kind    : Kind.t;
    flavour : Kind.Flavour.t;
  } [@@deriving show, sexp]

  let equal tv1 tv2 = tv1.id = tv2.id
  let compare tv1 tv2 = compare tv1.id tv2.id
end

(** Type constants have a name and a kind.
 *  Eg. $c^K$ *)
module TypeCon = struct
  type t = {
    name : Name.t;
    kind : Kind.t;
  } [@@deriving show, sexp]

  let equal tc1 tc2 = Name.equal tc1.name tc2.name
  let compare tc1 tc2 = Name.compare tc1.name tc2.name
end


(** Types in the paper were presented as:
 *
 * $\tau^K ::= \alpha^K$
 * $\qquad |\  c^K$
 * $\qquad |\  c^{K_0}\langle \tau_1^{K_1}, \ldots,$$\tau_n^{K_n} \rangle$
 *
 * where:
 * * $\alpha^k$ is a type variable, using $\mu$ for effects, $\xi$ for heaps
 * * $c^K$ is a type constant
 * * $K_0$ is C's type constructor kind, given by $K_0=(K_1,\ldots,K_n) \rightarrow K$
 * $K$ is a type's kind. The kind system gurantees that types $\tau$ are
 * well-formed. The formal definitions of kinds are:
 *      $K ::= * | e | k | h$                    : values, effect rows, effect constants, and heaps, respectively
 * $\quad\ |   (K_1,\ldots,K_n) \rightarrow K$   : type constructor
 **)
type typ =

  (**
   * $\forall a b c. \phi, \psi \Rightarrow \rho$
   * there is at least one variable
   * every variable occurs at least once in rho
   * variables and predicates are canonically ordered
   * each predicate refers to at least one of the variables.
   * Rho is really $\rho^\star$, where its kind is the set of all kinds (Kleene star) *)
  | TForall of TypeVar.t list * pred list * rho


  (** $(x:a, y:b, z:c) \rightarrow m\ d$ *)
  | TFun of ((Name.t * typ) list) * effect * typ

  (**  a type constant (primitive, label, or newtype; not $\rightarrow$ or $\Rightarrow$) *)
  | TCon of TypeCon.t

  (** type variable (cannot instantiate to $\rightarrow$ or $\Rightarrow$) *)
  | TVar of TypeVar.t

  (** application of datatypes *)
  | TApp of typ * (typ list)

  (**
   * type synonym indirection
   * first (type list) is the actual arguments
   * final typ is the "real" type (expanded) (it always has kind '$\star$' (Kleene star)) *)
  | TSyn of type_syn * (typ list) * typ

and pred = PredSub   of typ * typ
         | PredIFace of Name.t * typ list

(** Various synonyms of types *)
and scheme = typ
and sigma  = typ                (* polymorphic type *)
and tau    = typ                (* monomorphic type *)
and rho    = typ                (* unqualified type *)
and effect = tau

(** An inference type can contain type variables of flavour 'Meta' or 'Skolem' *)
and infer_type = typ


(**
 * The flavour of a type variable. Types in a 'Type.assumption' ($\Gamma$) and
 * inferred types in "Core.core" are always of the 'Bound' flavour.
 * 'Meta' and 'Skolem' type variables only ever occur during type inference. *)
(* TODO: Figure out why this was redeclared from Kind.flavour? *)
(* and flavour = Kind.Flavour.t *)


(** Type synonyms have an identifier, kind, and rank (used for partial ordering among type synonyms)
 * Eg. $\alpha^K_r$  *)
and type_syn = {
  type_syn_name : Name.t;
  type_syn_kind : Kind.t;
  type_syn_rank : synonym_rank;
  type_syn_info : syn_info option;
}


(** The rank of a type synonym gives a relative ordering among them. This is used
 * during unification to increase the chance of matching up type synonyms. *)
and synonym_rank = int


(*****************************************************************
   Information about types

   Defined here to avoid circular dependencies
 *****************************************************************)

(** Data type information: name, kind, type arguments, and constructors *)
and data_info = {
  data_info_sort    : Syntax.DataKind.t;
  data_info_name    : Name.t;
  data_info_kind    : Kind.t;
  data_info_params  : TypeVar.t list;       (** arguments *)
  data_info_constrs : con_info list;
  (* data_info_range   : range; *)         (** location information *)
  data_info_is_rec  : bool;                (** recursive?  *)
  data_info_is_open : bool;
  data_info_doc     : string
}

(** Constructor information: constructor name, name of the newtype,
 * field types, and the full type of the constructor *)
and con_info = {
  con_info_name : Name.t;
  con_info_type_name    : Name.t;
  (* con_info_type_sort : name *)
  con_info_exists       : TypeVar.t list;       (** existentials *)
  con_info_params       : (Name.t * typ) list;   (** field types *)
  con_info_type         : scheme;
  con_info_type_sort    : Syntax.DataKind.t;
  (* con_info_range        : range; *)         (** Source code position information *)
  (* con_info_param_ranges : range list; *)
  con_info_singleton    : bool;                (** is this the only constructor of this type? *)
  con_info_doc          : string
}

(** A type synonym is quantified by type parameters *)
and syn_info = {
  syn_info_name   : Name.t;
  syn_info_kind   : Kind.t;
  syn_info_params : TypeVar.t list;        (** parameters *)
  syn_info_typ    : typ;                  (** result type *)
  syn_info_rank   : synonym_rank;
  (* syn_info_range  : range; *)
  syn_info_doc    : string;
}

open Core

module rec Show_typ : BasicClasses.Show with type t = typ = struct
  type t = typ
  let show s =
    let rec show' = function
      | TForall (tvs, ps, r) -> "TForall"
      | TFun (nts,e,t) -> "TFun"
      | TCon tc -> "TCon"
      | TVar tv -> "TVar" (* " (" ^ Show ^")" *)
      | TApp (t,ts) -> Printf.sprintf "TApp (%s,%s)" (show' t) (List.to_string ts ~f:show')
      | TSyn (ts,tls,t) -> Printf.sprintf "TSyn (%s,%s,%s)"
                             (Show_type_syn.show ts) (List.to_string tls ~f:show') (show' t)
    in show' s
end

and Show_pred : BasicClasses.Show with type t = pred = struct
  type t = pred
  let show = function
    | PredSub (t1,t2) -> Printf.sprintf "PredSub (%s,%s)" (Show_typ.show t1) (Show_typ.show t2)
    | PredIFace (n,ts) ->
        Printf.sprintf "PredIFace (%s,%s)" (Name.show n) (List.to_string ts ~f:Show_typ.show)
end

and Show_type_syn : BasicClasses.Show with type t = type_syn = struct
  type t = type_syn
  let show s = Printf.sprintf "{ type_syn_name : %s; type_syn_kind : %s; type_syn_rank : %s; type_syn_info : %s }"
                 (Name.show s.type_syn_name) (Kind.show s.type_syn_kind)
                 (string_of_int s.type_syn_rank)
                 (match s.type_syn_info with None -> "None"
                                           | Some i -> "("^ Show_syn_info.show i ^")")
end

and Show_syn_info : BasicClasses.Show with type t = syn_info = struct
  type t = syn_info
  let show s = Printf.sprintf "{ name : %s; kind : %s; params : %s; typ : %s; rank : %s; doc : %s }"
                 (Name.show s.syn_info_name) (Kind.show s.syn_info_kind)
                 (List.to_string s.syn_info_params ~f:(fun e -> TypeVar.show e))
                 (Show_typ.show s.syn_info_typ) (string_of_int s.syn_info_rank)
                 s.syn_info_doc
end

let show_con_info (info:con_info) = Name.show info.con_info_name

let pp_con_info fmt info = Format.pp_print_string fmt @@ show_con_info info

let rec max_synonym_rank (tp:typ) : synonym_rank =
  let max_synonym_ranks : typ list -> int =
    List.fold_right ~f:(fun a b -> max (max_synonym_rank a) b) ~init:0
  in
  match tp with
  | TForall(_,_,rho)  -> max_synonym_rank rho
  | TFun(args,eff,tp) -> max_synonym_ranks (tp::eff::(List.map ~f:snd args))
  | TCon _            -> 0
  | TVar _            -> 0
  | TApp(tp,tps)      -> max_synonym_ranks (tp::tps)
  | TSyn(syn,args,tp) -> max syn.type_syn_rank (max_synonym_ranks @@ tp::args) (* TODO: replace nested destructure with proper accessor call *)

(***************************************************
   Predicates
 ***************************************************)

(** Is a type variable 'Bound'? *)
let is_bound tv =
  match tv.TypeVar.flavour with Bound -> true | _ -> false

(** Is a type variable 'Meta' (and thus unifiable) ? *)
let is_meta tv =
  match tv.TypeVar.flavour with Meta -> true | _ -> false

(** Is a type variable 'Skolem' (and thus not unifiable) ? *)
let is_skolem tv =
  match tv.TypeVar.flavour with Skolem -> true | _ -> false

(*****************************************************
   Equality
 *****************************************************)

let eq_type_syn ts1 ts2 = ts1.type_syn_name = ts2.type_syn_name
let compare_type_syn ts1 ts2 = Name.compare ts1.type_syn_name ts2.type_syn_name

(******************************************************
   Split/add quantifiers
 ******************************************************)

(** Split type into a list of universally quantified
 *  type variables, a list of predicates, and a rho-type.
 * $\tau^K \rightarrow ([\forall \alpha \beta \gamma \ldots], [pred], \rho$) *)
let rec split_pred_type (tp:typ) : (TypeVar.t list * pred list * rho) =
  (* We must split a synonym if its expansion
   * includes further quantifiers or predicates *)
  let rec must_split = function
    | TForall _    -> true
    | TSyn(_,_,tp) -> must_split tp
    | _            -> false
  in match tp with
  | TForall(vars,preds,rho)         -> (vars, preds, rho)
  | TSyn(_,_,tp) when must_split tp -> split_pred_type tp
  | tp                              -> ([], [], tp)

(** split a function type into its arguments, effect, and result type *)
let rec split_fun_type = function
  | TFun(args,effect,result) -> Some (args,effect,result)
  | TSyn(_,_,t)              -> split_fun_type t
  | _                        -> None


(* Find all quantified type variables, but do not expand synonyms *)
let shallow_split_vars = function
  | TForall(vars,preds,rho) -> (vars,preds,rho)
  | tp                      -> ([], [], tp)


(* Find all predicates *)
let shallow_split_preds = function
  | TForall(_,preds,_) -> preds
  | _                  -> []


let rec expand_syn = function
  | TSyn(syn,args,tp) -> expand_syn tp
  | tp                -> tp


let tForall (vars : TypeVar.t list) (preds : pred list) (rho : rho) : scheme =
  match (vars, preds) with
  | ([],[]) -> rho
  | _       -> TForall(vars,preds,rho)

(** Create a type scheme from a list of quantifiers *)
let make_scheme (vars : TypeVar.t list) (rho:rho) : scheme =
  let (vars0,preds,t) = split_pred_type rho in
  tForall (vars @ vars0) preds t

let quantify (vars : TypeVar.t list) (tp : scheme) : scheme =
  let (vars0,preds,rho) = split_pred_type tp in
  tForall (vars @ vars0) preds rho

let qualify (preds : pred list) (tp : scheme) : scheme =
  let (vars,preds0,rho) = split_pred_type tp in
  tForall vars (preds @ preds0) rho

let rec apply tp1 tp2 =
  let rec must_split = function
    | TApp(_,_)    -> true
    | TSyn(_,_,tp) -> must_split tp
    | _            -> false
  in match tp1 with
  | TApp(tp,tps)       -> TApp(tp, tps @ [tp2])
  | TSyn(_,_,tp)
    when must_split tp -> apply tp tp2
  | _                  -> TApp(tp1,[tp2])

let get_con_arities tp =
  let (tvars,preds,rho) = split_pred_type tp in
  match split_fun_type rho with
  | Some((pars,eff,res)) -> (List.length tvars, List.length pars)
  | None                 -> (List.length tvars, 0)


(****************************************************
   Assertions
 ****************************************************)

(** Is this a type variable? *)
let rec is_TVar = function
  | TVar(tv)    -> true
  | TSyn(_,_,t) -> is_TVar t
  | _           -> false

(** Is this a type constant? *)
let rec is_TCon = function
  | TCon(c)     -> true
  | TSyn(_,_,t) -> is_TCon t
  | _           -> false

(** Verify that a type is a $\rho$ type
 * i.e, no outermost quantifiers *)
let rec is_Rho = function
  | TForall _   -> false
  | TSyn(_,_,t) -> is_Rho t
  | _           -> true

(** Is this a type constant? *)
let rec is_Tau = function
  | TForall _    -> false
  | TFun(xs,e,r) -> List.for_all ~f:(fun x -> is_Tau @@ snd x) xs && is_Tau e && is_Tau r (* TODO: e should always be tau *)
  | TCon _       -> true
  | TVar _       -> true
  | TApp(a,b)    -> is_Tau a && List.for_all ~f:is_Tau b
  | TSyn(_,ts,t) -> is_TCon t


(** Is this a function type? *)
let rec is_Fun tp =
  match split_fun_type tp with
  | Some (args,effect,res) -> true
  | None                   -> false

(****************************************************
   Primitive types
 ****************************************************)

let tcon_int = TypeCon.{name = Name.tp_int; kind = Kind.Prim.star }

(** Type of integers (@Int@) *)
let type_int : tau = TCon(tcon_int)

let is_type_int = function
  | TCon(tc) -> tc = tcon_int
  | _        -> false

(** Type of floats *)
let type_float : tau = TCon{ name = Name.tp_float; kind = Kind.Prim.star}

let tcon_char : TypeCon.t = { name = Name.tp_char; kind = Kind.Prim.star}

(** Type of characters *)
let type_char : tau = TCon(tcon_char)

let is_type_char = function
  | TCon(tc) -> tc = tcon_char
  | _        -> false

let tcon_string : TypeCon.t = {name=Name.tp_string; kind=Kind.Prim.star}

(** Type of strings *)
let type_string : tau = TCon(tcon_string)

let label_name (tp : tau) : Name.t =
  match expand_syn tp with
  | TCon(tc) -> tc.TypeCon.name
  | TApp(TCon(tc),_) ->
      Failure.assertwith "non-expanded type synonym used as a label" (tc.TypeCon.name <> Name.effect_extend) tc.TypeCon.name
  | _ -> failwith "Type.Unify.label_name: label is not a constant"

let effect_empty : tau =
  TCon{name = Name.effect_empty; kind = Kind.Prim.effect }

let is_effect_empty (tp : tau) : bool =
  match expand_syn tp with
  | TCon tc -> tc.TypeCon.name = Name.effect_empty
  | _       -> false

let tcon_effect_extend : TypeCon.t =
  { name = Name.effect_extend; kind = (Kind.Prim.fun_1 Kind.Prim.label (Kind.Prim.fun_1 Kind.Prim.effect Kind.Prim.effect)) }

let rec extract_effect_extend (t : tau) : tau list * tau =
  let extract_label (l : tau) : tau list =
    match expand_syn l with
    | TApp(TCon(tc),[_;e]) when tc.name = Name.effect_extend ->
        let (ls,tl) = extract_effect_extend l in
        Failure.assertwith "label was not a fixed effect type alias" (is_effect_fixed tl) ls
    | _ -> [l]
  in
  match expand_syn t with
  | TApp(TCon(tc),[l;e]) when tc.name = Name.effect_extend ->
      let (ls,tl) = extract_effect_extend e in
      let ls0 = extract_label l in
      (ls0 @ ls, tl)
  | _ -> ([],t)

and is_effect_fixed (tp : tau) : bool =
  is_effect_empty (snd (extract_effect_extend tp))


let rec effect_extend (label : tau) (eff : tau) : tau =
  let (ls,tl) = extract_effect_extend label in
  if List.is_empty ls then
    TApp(TCon(tcon_effect_extend), [label;eff])
  else effect_extends ls eff

(* prevent over expansion of type synonyms here (see also: Core.Parse.teffect) *)
and effect_extends (labels : tau list) (eff : tau) : tau =
  match labels with
  | [TSyn({type_syn_kind=kind;_},_,_) as lab] when is_effect_empty eff && kind = Kind.Prim.effect -> lab
  | _ -> List.fold_right ~f:effect_extend ~init:eff labels

let effect_fixed (labels : tau list) : tau = effect_extends labels effect_empty

(* let rec effect_extend_no_dup (label : tau) (eff : tau) : tau = *)
(*   let (ls,_) = extract_effect_extend eff in *)
(*   if List.is_empty ls then *)
(*     let (els,_) = extract_effect_extend eff in *)
(*     if List.mem els label ~equal:Eq_typ.equal then *)
(*       eff *)
(*     else TApp(TCon tcon_effect_extend,[label;eff]) *)
(*   else effect_extend_no_dups ls eff *)

(* and effect_extend_no_dups (labels : tau list) (eff : tau) : tau = *)
(*   List.fold_right ~f:effect_extend_no_dup ~init:eff labels *)

let rec shallow_extract_effect_extend : tau -> tau list * tau = function
  | TApp(TCon(tc),[l;e]) when tc.name = Name.effect_extend ->
      let (ls,tl) = shallow_extract_effect_extend e in
      (l::ls, tl)
  | t -> ([],t)

and shallow_effect_extend (label : tau) (eff : tau) : tau =
  (* We do not expand type synonyms in the label here by using the 'shallow' version of extract
   * this means that type synonyms of kind E (i.e. a fixed effect row) could stay around in
   * the label (which should have kind X).
   * We use this to keep type synonyms around longer -- but during unification we've got to be
   * careful to expand such synonyms*)
  let (ls,tl) = shallow_extract_effect_extend label in
  if List.is_empty ls
  then TApp(TCon(tcon_effect_extend),[label;eff])
  else effect_extends ls eff



let extract_ordered_effect (tp : tau) : (tau list * tau) =
  let expand l =
    let (ls,tl) = extract_effect_extend l in
    if is_effect_empty tl && not (List.is_empty ls)
    then ls
    else [l]
  in
  let (labs,tl) = extract_effect_extend tp in
  let labss     = List.concat_map ~f:expand labs in
  let slabs     = List.dedup_and_sort ~compare:(fun l1 l2 -> Name.compare (label_name l1) (label_name l2)) labss in
  (slabs,tl)


let order_effect (tp : tau) : tau =
  let (ls,tl) = extract_ordered_effect tp in
  List.fold_right ~f:effect_extend ~init:tl ls

(** A type in canonical form has no type synonyms and expanded effect types *)
let rec canonical_form : typ -> typ = function
  | TSyn(syn,args,t)      -> canonical_form t (* You can see how here, we abandon the synonym for the raw type *)
  | TForall(vars,preds,t) -> TForall(vars, preds, canonical_form t)
  | TApp(t,ts)            -> TApp(canonical_form t, List.map ~f:canonical_form ts)
  | TFun(args,eff,res)    -> TFun(List.map ~f:(fun (name,t) -> (name, canonical_form t)) args,
                                  (order_effect @@ canonical_form eff),
                                  (canonical_form res))
  | tp -> tp


(** A type in minimal form is canonical_form but also has no named function arguments *)
let minimal_form : typ -> typ = function
  | TSyn(syn,args,t)      -> canonical_form t
  | TForall(vars,preds,t) -> TForall(vars,preds,canonical_form t)
  | TApp(t,ts)            -> TApp(canonical_form t, List.map ~f:canonical_form ts)
  | TFun(args,eff,res)    -> TFun(List.map ~f:(fun (_,t) -> (Name.null, canonical_form t)) args,
                                  (order_effect @@ canonical_form eff),
                                  (canonical_form res))
  | tp -> tp

(***********************************************
   Primitive Types Cont.
 ***********************************************)

let single (name : Name.t) : effect =
  effect_extend (TCon { name; kind = Kind.Prim.effect }) effect_empty

let type_divergent : tau = single Name.tp_div

let tcon_total : TypeCon.t = {name=Name.effect_empty; kind=Kind.Prim.effect }

let type_total : tau = TCon tcon_total

let is_type_total : tau -> bool = function
  | TCon tc -> tc = tcon_total
  | _       -> false

let type_partial : tau = single Name.tp_partial

let type_pure : tau = effect_fixed [type_partial; type_divergent]

let tcon_bool : TypeCon.t = { name=Name.tp_bool; kind = Kind.Prim.star}
let type_bool : tau = TCon tcon_bool

let is_type_bool : tau -> bool = function
  | TCon tc -> tc = tcon_bool
  | _       -> false

let tcon_unit : TypeCon.t = { name = Name.tp_unit; kind = Kind.Prim.star }
let type_unit : tau  = TCon tcon_unit

let is_type_unit : tau -> bool = function
  | TCon tc -> tc = tcon_unit
  | _       -> false

let tcon_list : TypeCon.t = {
  name = Name.tp_list;
  kind = (Kind.Prim.fun_1 Kind.Prim.star Kind.Prim.star)
}

(** Type of lists (@[]@) *)
let type_list = TCon tcon_list

let type_fun args effect result =
  TFun(args,effect,result)

(** Create an application *)
let type_app t ts =
  match (t,ts) with
  | (_,[])           -> t
  | (TApp(t1,ts0),_) -> TApp(t1,(ts0 @ ts))
  | (_,_)            -> TApp(t,ts)

let type_void : tau = TCon { name = Name.tp_void; kind = Kind.Prim.star }

let type_tuple (n : int) : tau =
  TCon { name = (Name.tuple n); kind = (Kind.Prim.arrow_n n)}

let tcon_optional : TypeCon.t = {
  name = Name.tp_optional;
  kind = (Kind.Prim.fun_1 Kind.Prim.star Kind.Prim.star)
}

let type_optional : tau = TCon tcon_optional

let is_optional (tp : typ) : bool =
  match expand_syn tp with
  | TApp(TCon tc,[t]) -> tc = tcon_optional
  | _ -> false

let make_optional (tp : typ) : typ =
  TApp(type_optional, [tp])

let unoptional (tp : typ) : typ =
  match expand_syn tp with
  | TApp((TCon tc),[t]) when tc = tcon_optional -> t
  | _ -> tp

(** Remove type synonym indirections *)
let rec pruneSyn : rho -> rho = function
  | TSyn(sin,args,t) -> pruneSyn t
  | TApp(t1,ts)      -> TApp((pruneSyn t1), (List.map ~f:pruneSyn ts))
  | rho              -> rho


(*****************************************************
   Conversion between types
 *****************************************************)
module type IsType = sig
  type t
  (* Trivial conversion to a kind quantified type scheme *)
  val to_type : t -> typ
end

(* let to_type {I:IsType} tp = I.to_type tp *)

module IsType_typ : IsType with type t = typ = struct
  type t = typ
  let to_type tp = tp
end

module IsType_type_var : IsType with type t = TypeVar.t = struct
  type t = TypeVar.t
  let to_type v = TVar v
end

module IsType_type_con : IsType with type t = TypeCon.t = struct
  type t = TypeCon.t
  let to_type con = TCon con
end 

(******************************************************
   Equality between types
 ******************************************************)
let rec match_type tp1 tp2 =
  match (expand_syn tp1, expand_syn tp2) with
  | (TForall(vs1,ps1,t1), TForall(vs2,ps2,t2)) -> (vs1 = vs2 && match_preds ps1 ps2 && match_type t1 t2)
  | (TFun(pars1,eff1,t1),TFun(pars2,eff2,t2))  -> (match_types (List.map pars1 ~f:snd) (List.map ~f:snd pars2) && match_effect eff1 eff2 && match_type t1 t2)
  | (TCon(c1),TCon(c2))                        -> c1 = c2
  | (TVar(v1),TVar(v2))                        -> v1 = v2
  | (TApp(t1,ts1),TApp(t2,ts2))                -> (match_type t1 t2 && match_types ts1 ts2)
  (* | (TSyn(syn1,ts1,t1),TSyn(syn2,ts2,t2))      -> (syn1 = syn2 && match_types ts1 ts2 && match_type t1 t2) *)
  | _ -> false

and match_types ts1 ts2 =
  List.fold2_exn ts1 ts2 ~init:true ~f:(fun i l r -> i && (match_type l r))

and match_effect eff1 eff2 =
  match_type (order_effect eff1) (order_effect eff2)

and match_pred p1 p2 =
  match (p1,p2) with
  | (PredSub(sub1,sup1), PredSub(sub2,sup2)) -> (match_type sub1 sub2 && match_type sup1 sup2)
  | (PredIFace(n1,ts1), PredIFace(n2,ts2))   -> (n1 = n2 && match_types ts1 ts2)
  | _ -> false

and match_preds ps1 ps2 =
  List.fold2_exn ps1 ps2 ~init:true ~f:(fun i l r -> i && (match_pred l r))

(* implicit *)
module Eq_typ : BasicClasses.Eq with type t = typ = struct
  type t = typ
  let equal = match_type
end

(* implicit *)
module Eq_pred : BasicClasses.Eq with type t = pred = struct
  type t = pred
  let equal = match_pred
end

module Flavour = Kind.Flavour

let pred_type = function
  | PredSub (t1,t2) -> type_fun [(Name.create "sub", t1)] type_total t2
  | PredIFace (name, tps) -> Failure.todo "Type.Operations.predType.PredIFace"
