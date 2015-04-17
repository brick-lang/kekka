open Name
open Name_prim
open Id
open Kind
open Syntax
open Failure

(*
 * types.ml
 * Ported from Daan Leijin's implementation,
 * which is licensed under the Apache License
 *)

(** This is the primary type-system, the heart of \lambda^k *)


(** Types in the paper were presented like this :
  * types  \tau^K ::= \alpha^K   --|type variable (using \mu for effects, \xi for heaps)
  *               |   c^K        --|type constant
  *               |   c^{K_0}\langle \tau_1^{K_1}, \ldots, \tau_n^{K_n} \rangle  --| where K_0 is C's type constructor kind, given by K_0=(K_1,\ldots,K_n) \rightarrow K
  * where \it{K} is a type's kind. The kind system gurantees that types \tau are
  * well-formed. The formal definitions of kinds are:
  * kinds       K ::= * | e | k | h                    --|values, effect rows, effect constants, and heaps, respectively
  *               |   (K_1,\ldots,K_n) \rightarrow K   --|type constructor
  **)
type typ =

  (**
   * \forall a b c. \phi, \psi \Rightarrow \rho
   * there is at least one variable
   * every variable occurs at least once in rho
   * variables and predicates are canonically ordered
   * each predicate refers to at least one of the variables.
   * Rho is really \rho^*, where its kind is the set of all kinds (Kleene star) *)
  | TForall of type_var list * pred list * rho


  (** (x:a, y:b, z:c) -> m d *)
  | TFun of ((name * typ) list) * effect * typ

  (**  a type constant (primitive, label, or newtype; not \rightarrow or \Rightarrow *)
  | TCon of type_con

  (** type variable (cannot instantiate to \rightarrow or \Rightarrow) *)
  | TVar of type_var

  (** application of datatypes *)
  | TApp of typ * (typ list)

  (**
   * type synonym indirection
   * first (type list) is the actual arguments
   * final typ is the "real" type (expanded) (it always has kind '*' (Kleene star)) *)
  | TSyn of type_syn * (typ list) * typ
              [@@deriving show]

and pred = PredSub   of typ * typ
         | PredIFace of name * typ list
                          [@@deriving show]

(** Various synonyms of types *)
and scheme = typ
and sigma  = typ                (* polymorphic type *)
and tau    = typ                (* monomorphic type *)
and rho    = typ                (* unqualified type *)
and effect = tau

(** An inference type can contain type variables of flavour 'Meta' or 'Skolem' *)
and infer_type = typ

(**
 * Type variables are variables in a type and contain an identifier and
 * kind. One can ask for the free type variables in a type, and substitute
 * them with '\tau' types.
 * Eg. \alpha^K *)
and type_var = {
  type_var_id      : id;
  type_var_kind    : kind;
  type_var_flavour : flavour;
} [@@deriving show]

(**
 * The flavour of a type variable. Types in a 'Type.assumption' (\gamma) and
 * inferred types in "Core.core" are always of the 'Bound' flavour.
 * 'Meta' and 'Skolem' type variables only ever occur during type inference. *)
and flavour = Meta
            | Skolem
            | Bound
                [@@deriving eq,ord,show]

(** Type constants have a name and a kind.
 *  Eg. c^K *)
and type_con =  {
  type_con_name : name;
  type_con_kind : kind;
} [@@deriving show]

(** Type synonyms have an identifier, kind, and rank (used for partial ordering among type synonyms)
  * Eg. \alpha^K_r  *)
and type_syn = {
  type_syn_name : name;
  type_syn_kind : kind;
  type_syn_rank : synonym_rank;
  type_syn_info : syn_info option;
} [@@deriving show]


(** The rank of a type synonym gives a relative ordering among them. This is used
  * during unification to increase the chance of matching up type synonyms. *)
and synonym_rank = int


(*****************************************************************
   Information about types

   Defined here to avoid circular dependencies
 *****************************************************************)

(** Data type information: name, kind, type arguments, and constructors *)
and data_info = {
  data_info_sort    : data_kind;
  data_info_name    : name;
  data_info_kind    : kind;
  data_info_params  : type_var list;       (** arguments *)
  data_info_constrs : con_info list;
  (* data_info_range   : range; *)         (** location information *)
  data_info_is_rec  : bool;                (** recursive?  *)
  data_info_doc     : string
}

(** Constructor information: constructor name, name of the newtype,
  * field types, and the full type of the constructor *)
and con_info = {
  con_info_name : name;
  con_info_type_name    : name;
  (* con_info_type_sort : name *)
  con_info_exists       : type_var list;       (** existentials *)
  con_info_params       : (name * typ) list;   (** field types *)
  con_info_type         : scheme;
  con_info_type_sort    : data_kind;
  (* con_info_range        : range; *)         (** Source code position information *)
  (* con_info_param_ranges : range list; *)
  con_info_singleton    : bool;                (** is this the only constructor of this type? *)
  con_info_doc          : string
}

(** A type synonym is quantified by type parameters *)
and syn_info = {
  name   : name;
  kind   : Kind.kind;
  params : type_var list;        (** parameters *)
  typ    : typ;                  (** result type *)
  rank   : synonym_rank;
  (* range  : range; *)
  doc    : string;
} [@@deriving show]

open Core.Std

let show_con_info (info:con_info) = show_name info.con_info_name

let pp_con_info fmt info = Format.pp_print_string fmt @@ show_con_info info

let rec max_synonym_rank (tp:typ) : int =
  let max_synonym_ranks  : typ list -> int =
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
  match tv.type_var_flavour with Bound -> true | _ -> false

(** Is a type variable 'Meta' (and thus unifiable) ? *)
let is_meta tv =
  match tv.type_var_flavour with Meta -> true | _ -> false

(** Is a type variable 'Skolem' (and thus unifiable) ? *)
let is_skolem tv =
  match tv.type_var_flavour with Skolem -> true | _ -> false


(*****************************************************
   Equality
 *****************************************************)

let eq_type_var tv1 tv2 = tv1.type_var_id = tv2.type_var_id
let compare_type_var tv1 tv2 = compare tv1.type_var_id tv2.type_var_id

let eq_type_con tc1 tc2 = tc1.type_con_name = tc2.type_con_name
let compare_type_var tc1 tc2 = compare tc1.type_con_name tc2.type_con_name

let eq_type_syn ts1 ts2 = ts1.type_syn_name = ts2.type_syn_name
let compare_type_var ts1 ts2 = compare ts1.type_syn_name ts2.type_syn_name

(******************************************************
   Split/add quantifiers
 ******************************************************)

(** Split type into a list of universally quantified
  *  type variables, a list of predicates, and a rho-type.
  * \tau^K \rightarrow [\forall \alpha \beta \gamma \ldots] [pred] \rho *)
let rec split_pred_type =
  (* We must split a synonym if its expansion
   * includes further quantifiers or predicates *)
  let rec must_split = function
    | TForall _    -> true
    | TSyn(_,_,tp) -> must_split tp
    | _            -> false
  in
  function
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


let tForall (vars : type_var list) (preds : pred list) (rho : rho) : scheme =
  match (vars, preds) with
  | ([],[]) -> rho
  | _       -> TForall(vars,preds,rho)

(** Create a type scheme from a list of quantifiers *)
let make_scheme (vars : type_var list) (rho:rho) : scheme =
  let (vars0,preds,t) = split_pred_type rho in
  tForall (vars @ vars0) preds t

let quantify_type (vars : type_var list) (tp : scheme) : scheme =
  let (vars0,preds,rho) = split_pred_type tp in
  tForall (vars @ vars0) preds rho

let qualify_type (preds : pred list) (tp : scheme) : scheme =
  let (vars,preds0,rho) = split_pred_type tp in
  tForall vars (preds @ preds0) rho

let rec apply_type tp1 tp2 =
  let rec must_split = function
    | TApp(_,_)    -> true
    | TSyn(_,_,tp) -> must_split tp
    | _            -> false
  in match tp1 with
  | TApp(tp,tps)       -> TApp(tp, tps @ [tp2])
  | TSyn(_,_,tp)
    when must_split tp -> apply_type tp tp2
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

(** Verify that a type is a \rho type
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

let tcon_int = { type_con_name = name_tp_int; type_con_kind = kind_star}

(** Type of integers (@Int@) *)
let type_int : tau = TCon(tcon_int)

let is_type_int = function
  | TCon(tc) -> tc = tcon_int
  | _        -> false

(** Type of floats *)
let type_float : tau = TCon({ type_con_name = name_tp_float; type_con_kind = kind_star})

let tcon_char = { type_con_name = name_tp_char; type_con_kind = kind_star}

(** Type of characters *)
let type_char : tau = TCon(tcon_char)

let is_type_char = function
  | TCon(tc) -> tc = tcon_char
  | _        -> false
;;

let tcon_string = { type_con_name = name_tp_string; type_con_kind = kind_star};;

(** Type of strings *)
let type_string : tau = TCon(tcon_string)

let label_name (tp : tau) : name =
  match expand_syn tp with
  | TCon(tc) -> tc.type_con_name
  | TApp(TCon(tc),_) -> assertion "non-expanded type synonym used as a label" (tc.type_con_name <> name_effect_extend) tc.type_con_name
  | _                -> failure "Type.Unify.label_name: label is not a constant"

let effect_empty : tau =
  TCon({ type_con_name = name_effect_empty; type_con_kind = kind_effect })

let is_effect_empty (tp : tau) : bool =
  match expand_syn tp with
  | TCon tc -> tc.type_con_name = name_effect_empty
  | _       -> false

let tcon_effect_extend : type_con =
  { type_con_name = name_effect_extend; type_con_kind = (kind_fun kind_label (kind_fun kind_effect kind_effect)) }

let rec extract_effect_extend (t : tau) : tau list * tau =
  let extract_label (l : tau) : tau list =
    match expand_syn l with
    | TApp(TCon(tc),[_;e]) when tc.type_con_name = name_effect_extend ->
      let (ls,tl) = extract_effect_extend l in
      assertion "label was not a fixed effect type alias" (is_effect_fixed tl) ls
    | _ -> [l]
  in
  match expand_syn t with
  | TApp(TCon(tc),[l;e]) when tc.type_con_name = name_effect_extend ->
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
  | [TSyn({type_syn_kind=kind;_},_,_) as lab] when is_effect_empty eff && kind = kind_effect -> lab
  | _ -> List.fold_right ~f:effect_extend ~init:eff labels

let effect_fixed (labels : tau list) : tau = effect_extends labels effect_empty

let rec effect_extend_no_dup (label : tau) (eff : tau) : tau =
  let (ls,_) = extract_effect_extend eff in
  if List.is_empty ls then
    let (els,_) = extract_effect_extend eff in
    if List.mem els label
    then eff
    else TApp(TCon tcon_effect_extend,[label;eff])
  else effect_extend_no_dups ls eff

and effect_extend_no_dups (labels : tau list) (eff : tau) : tau =
  List.fold_right ~f:effect_extend_no_dup ~init:eff labels

let rec shallow_extract_effect_extend : tau -> tau list * tau = function
  | TApp(TCon(tc),[l;e]) when tc.type_con_name = name_effect_extend ->
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
  let slabs     = List.dedup @@ List.sort ~cmp:(fun l1 l2 -> compare (label_name l1) (label_name l2)) labss in
  (slabs,tl)


let order_effect (tp : tau) : tau =
  let (ls,tl) = extract_ordered_effect tp in
  List.fold_right ~f:effect_extend ~init:tl ls

(** A type in canonical form has no type synonyms and expanded effect types *)
let rec canonical_form = function
  | TSyn(syn,args,t)      -> canonical_form t (* You can see how here, we abandon the synonym for the raw type *)
  | TForall(vars,preds,t) -> TForall(vars, preds, canonical_form t)
  | TApp(t,ts)            -> TApp(canonical_form t, List.map ~f:canonical_form ts)
  | TFun(args,eff,res)    -> TFun(List.map ~f:(fun (name,t) -> (name, canonical_form t)) args,
                                  (order_effect @@ canonical_form eff),
                                  (canonical_form res))
  | tp -> tp


(** A type in minimal form is canonical_form but also has no named function arguments *)
let minimal_form = function
  | TSyn(syn,args,t)      -> canonical_form t
  | TForall(vars,preds,t) -> TForall(vars,preds,canonical_form t)
  | TApp(t,ts)            -> TApp(canonical_form t, List.map ~f:canonical_form ts)
  | TFun(args,eff,res)    -> TFun(List.map ~f:(fun (_,t) -> (name_null, canonical_form t)) args,
                                  (order_effect @@ canonical_form eff),
                                  (canonical_form res))
  | tp -> tp

(***********************************************
   Primitive Types Cont.
 ***********************************************)

let single (name : name) : effect =
  effect_extend (TCon { type_con_name = name; type_con_kind = kind_effect }) effect_empty

let type_divergent : tau = single name_tp_div

let tcon_total = { type_con_name = name_effect_empty; type_con_kind = kind_effect }

let type_total : tau = TCon tcon_total

let is_type_total : tau -> bool = function
  | TCon tc -> tc = tcon_total
  | _       -> false

let type_partial : tau = single name_tp_partial

let type_pure : tau = effect_fixed [type_partial; type_divergent]

let tcon_bool : type_con = { type_con_name = name_tp_bool; type_con_kind = kind_star }
let type_bool : tau = TCon tcon_bool

let is_type_bool : tau -> bool = function
  | TCon tc -> tc = tcon_bool
  | _       -> false

let tcon_unit : type_con = { type_con_name = name_tp_unit; type_con_kind = kind_star }

let type_unit : tau  = TCon tcon_unit

let is_type_unit : tau -> bool = function
  | TCon tc -> tc = tcon_unit
  | _       -> false

let tcon_list : type_con = {
  type_con_name = name_tp_list;
  type_con_kind = (kind_fun kind_star kind_star)
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

let type_void : tau = TCon { type_con_name = name_tp_void; type_con_kind = kind_star }

let type_tuple (n : int) : tau =
  TCon { type_con_name = (name_tuple n); type_con_kind = (kind_arrow_n n)}

let tcon_optional : type_con = {
  type_con_name = name_tp_optional;
  type_con_kind = (kind_fun kind_star kind_star)
}

let type_optional : tau = TCon tcon_optional

let is_optional (tp : tau) : bool =
  match expand_syn tp with
  | TApp(TCon tc,[t]) -> tc = tcon_optional
  | _ -> false

let make_optional (tp : tau) : tau =
  TApp(type_optional, [tp]) 

