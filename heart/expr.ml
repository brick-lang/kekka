open Core
open Common

type tname = Name.t * Type.typ 

(************************************************
 * Type definitions
 ************************************************)

module TypeDef = struct
  type t =
    | Synonym of { syn_info : Type.syn_info;
                   vis      : Syntax.visibility }

    | Data    of { data_info : Type.data_info;
                   vis       : Syntax.visibility;
                   con_vis   : Syntax.visibility list;
                   is_extend : bool } (* true if this is an extension of the datatype *)
  type group  = t list
  type groups = group list
end

(************************************************
 * Data representation
 ************************************************)
type con_repr =
  | ConEnum      of {con_type_name : Name.t; con_tag : int} (* part of enumeration (none has fields) *)
  | ConIso       of {con_type_name : Name.t; con_tag : int} (* one constructor with one field *)
  | ConSingleton of {con_type_name : Name.t; con_tag : int} (* the only constructor without fields *)
  | ConSingle    of {con_type_name : Name.t; con_tag : int} (* there is only one constructor  *)
  | ConStruct    of {con_type_name : Name.t; con_tag : int} (* constructor as value type *)
  | ConAsCons    of {con_type_name : Name.t; con_tag : int; (* constructor is the cons node of a list-like datatype  (may have one or more fields) *)
                     con_as_nil: Name.t } 
  | ConOpen      of {con_type_name : Name.t}                (* constructor of open data type *)
  | ConNormal    of {con_type_name : Name.t; con_tag : int} (* a regular constructor *)


(****************************************************************************
 * Expressions
 *
 * Since this is System-F, all binding sites are annotated with their type. 
 ****************************************************************************)
type expr =
  | Lam of tname list * Type.effect * expr

  (* typed name and possible type-arity/parameter-arity tuple for top-level functions *) 
  | Var of { var_name : tname; var_info : var_info}
  | App of expr * (expr list)

  (* Type (universal) abstraction application *)
  | TypeLam of Type.type_var list * expr
  | TypeApp of expr * (Type.typ list)

  (* Literals, constants, and labels *)
  | Constructor of { con_name : tname; con_repr : con_repr}
  | Literal of literal

  (* Let *)
  | Let of def_group list * expr

  (* Case expressions *)
  | Case of { case_exprs : expr list; case_branches : branch list}

and var_info =
  | InfoNone
  | InfoArity of int * int      (* type-parameters-arity, parameters-arity*)
  | InfoExternal of (Syntax.target * string) list

and branch = {
  branch_patterns : pattern list;
  branch_guards : guard list;
}

and guard = {
  guard_test : expr;
  guard_expr : expr;
}

and pattern =
  | PatConstructor of { pat_con_name : tname
                   ; pat_con_patterns : pattern list
                   ; pat_con_repr : con_repr
                   ; pat_type_args : Type.typ list
                   ; pat_type_res : Type.typ
                   (* ; pat_con_info : con_info *)
                   }

  | PatVariable of { pat_name : tname; pat_pattern : pattern }
  | PatLiteral of { pat_lit : literal }
  | PatWild
and literal =
  | Int of int
  | Float of float
  | Char of char
  | String of string

and def = {
  def_name : Name.t;
  def_type : Type.scheme;
  def_expr : expr;
  def_vis : Syntax.visibility;
  (* def_sort : def_sort; *)
  (* def_name_range : range; *)
  def_doc : string;
}

and def_group =
  | DefRec of def list
  | DefNonRec of def

(* Create a phantom application that opens the effect type of a function *)
let open_effect_expr
      (eff_from : Type.effect) (eff_to : Type.effect)
      (tp_from : Type.typ) (tp_to : Type.typ)
      (expr : expr) : expr =
  let open Type in
  let a : type_var = { type_var_id = -1; type_var_kind = Kind.kind_effect; type_var_flavour = Bound } in
  let b : type_var = { type_var_id = -2; type_var_kind = Kind.kind_effect; type_var_flavour = Bound } in
  (* forall a b. fun(x:tp_from)-> tp_to[total] *)
  let tp_open : typ = TForall([a;b], [], TFun([(Name.create "x", tp_from)], Type.type_total, tp_to)) in
  let var_open : expr = Var { var_name = (Name_prim.name_effect_open, tp_open)
                            ; var_info = (InfoExternal [(Default, "#1")])}
  in
  App ((TypeApp(var_open, [eff_from; eff_to])), [expr])

(***********************************************************
 * Auxiliary functions to build Heart terms
 ***********************************************************)

(** Add kind and type application  *)
let add_type_apps (ts: Type.type_var list) (e:expr) : expr = match (ts,e) with 
  | ([], e) -> e
  | (ts, TypeApp(e, args)) -> TypeApp(e, args @ List.map ts ~f:(fun t -> Type.TVar t))
  | (ts, e) -> TypeApp(e, List.map ts ~f:(fun t -> Type.TVar t))

let add_type_lambdas (pars: Type.type_var list) (e:expr) : expr = match (pars, e) with
  | ([], e) -> e
  | (pars, TypeLam(ps, e)) -> TypeLam(pars @ ps, e)
  | (pars, e) -> TypeLam(pars, e)
  

(** Create a fresh variable name with a particular prefix *)
let fresh_name (prefix:string) : Name.t =
  Name.create (prefix ^ "." ^ string_of_int (Unique.unique ()))
