open Core

type tname = Name.name * Type.typ 

type con_repr =
  | Enum of {con_type_name : Name.name; con_tag : int}
  | Iso of {con_type_name : Name.name; con_tag : int}
  | Singleton of {con_type_name : Name.name; con_tag : int}
  | Single of {con_type_name : Name.name; con_tag : int}
  | Struct of {con_type_name : Name.name; con_tag : int}
  | AsCons of {con_type_name : Name.name; con_as_nill: Name.name; con_tag : int}
  | Open of {con_type_name : Name.name}
  | Normal of {con_type_name : Name.name; con_tag : int}

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
  def_name : Name.name;
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
let fresh_name (prefix:string) : Name.name =
  Name.create (prefix ^ "." ^ string_of_int (Unique.unique ()))

module HasTypeVar_tname = struct
  type t = tname
  let substitute sub (name, tp) = (name, TypeVar.HasTypeVar_typ.substitute sub tp)
  let ftv (name, tp) = TypeVar.HasTypeVar_typ.ftv tp
  let btv (name, tp) = TypeVar.HasTypeVar_typ.btv tp
end

module HasTypeVar_list_tname = TypeVar.HasTypeVar_list(HasTypeVar_tname)

module rec HasTypeVar_def : TypeVar.HasTypeVar with type t = def = struct
  type t = def
  let substitute sub (def:def) = {def with def_type=TypeVar.HasTypeVar_typ.substitute sub def.def_type;
                                  def_expr=HasTypeVar_expr.substitute sub def.def_expr}
  let ftv def = TypeVar.tvs_union (TypeVar.HasTypeVar_typ.ftv def.def_type) (HasTypeVar_expr.ftv def.def_expr)
  let btv def = TypeVar.tvs_union (TypeVar.HasTypeVar_typ.btv def.def_type) (HasTypeVar_expr.btv def.def_expr)
end

and HasTypeVar_list_def : TypeVar.HasTypeVarEx with type t = def list
  = TypeVar.HasTypeVar_list(HasTypeVar_def)

and HasTypeVar_defgroup : TypeVar.HasTypeVar = struct
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

and HasTypeVar_list_defgroup : TypeVar.HasTypeVarEx with type t = def_group list
  = TypeVar.HasTypeVar_list(HasTypeVar_defgroup)

and HasTypeVar_pattern : TypeVar.HasTypeVar with type t = pattern = struct
  type t = pattern
  let rec substitute sub = function
    | PatVariable pvar -> PatVariable{pat_name = HasTypeVar_tname.substitute sub pvar.pat_name;
                                      pat_pattern = substitute sub pvar.pat_pattern}
    | PatConstructor con -> PatConstructor{con with pat_con_name = HasTypeVar_tname.substitute sub con.pat_con_name;
                                                    pat_con_patterns = HasTypeVar_list_pattern.substitute sub con.pat_con_patterns;
                                                    pat_type_args = TypeVar.HasTypeVar_list_typ.substitute sub con.pat_type_args;
                                                    pat_type_res = TypeVar.HasTypeVar_typ.substitute sub con.pat_type_res}
    | PatWild -> PatWild
    | PatLiteral lit -> PatLiteral lit

  let rec ftv = function
    | PatVariable pvar -> TypeVar.tvs_union (HasTypeVar_tname.ftv pvar.pat_name) (ftv pvar.pat_pattern)
    | PatConstructor con -> TypeVar.tvs_unions [HasTypeVar_tname.ftv con.pat_con_name;
                                                HasTypeVar_list_pattern.ftv con.pat_con_patterns;
                                                TypeVar.HasTypeVar_list_typ.ftv con.pat_type_args;
                                                TypeVar.HasTypeVar_typ.ftv con.pat_type_res]
    | PatWild -> TypeVar.tvs_empty
    | PatLiteral _ -> TypeVar.tvs_empty

  let rec btv = function
    | PatVariable pvar -> TypeVar.tvs_union (HasTypeVar_tname.btv pvar.pat_name) (btv pvar.pat_pattern)
    | PatConstructor con -> TypeVar.tvs_unions [HasTypeVar_tname.btv con.pat_con_name;
                                                HasTypeVar_list_pattern.btv con.pat_con_patterns;
                                                TypeVar.HasTypeVar_list_typ.btv con.pat_type_args;
                                                TypeVar.HasTypeVar_typ.btv con.pat_type_res]
    | PatWild -> TypeVar.tvs_empty
    | PatLiteral _ -> TypeVar.tvs_empty
end 

and HasTypeVar_list_pattern : TypeVar.HasTypeVarEx with type t = pattern list
  = TypeVar.HasTypeVar_list(HasTypeVar_pattern)

and HasTypeVar_guard : TypeVar.HasTypeVar with type t = guard = struct
  type t = guard
  let substitute sub {guard_test; guard_expr} = {guard_test=HasTypeVar_expr.substitute sub guard_test;
                                                 guard_expr=HasTypeVar_expr.substitute sub guard_expr;}
  let ftv {guard_test; guard_expr} = TypeVar.tvs_union (HasTypeVar_expr.ftv guard_test) (HasTypeVar_expr.ftv guard_expr)
  let btv {guard_test; guard_expr} = TypeVar.tvs_union (HasTypeVar_expr.btv guard_test) (HasTypeVar_expr.btv guard_expr)
end

and HasTypeVar_list_guard : TypeVar.HasTypeVarEx with type t = guard list
  = TypeVar.HasTypeVar_list(HasTypeVar_guard)

and HasTypeVar_branch : TypeVar.HasTypeVar with type t = branch = struct
  type t = branch
  let substitute sub {branch_patterns=patterns; branch_guards=guards} =
    let sub' = TypeVar.sub_remove (TypeVar.tvs_list @@ HasTypeVar_list_pattern.btv patterns) sub in
    { branch_patterns=List.map ~f:(HasTypeVar_pattern.substitute sub) patterns;
      branch_guards=List.map ~f:(HasTypeVar_guard.substitute sub') guards }

  let ftv {branch_patterns; branch_guards} =
    TypeVar.tvs_union
      (HasTypeVar_list_pattern.ftv branch_patterns)
      (TypeVar.tvs_diff
         (HasTypeVar_list_guard.ftv branch_guards)
         (HasTypeVar_list_pattern.btv branch_patterns))

  let btv {branch_patterns; branch_guards} =
    TypeVar.tvs_union (HasTypeVar_list_pattern.btv branch_patterns) (HasTypeVar_list_guard.btv branch_guards)
end

and HasTypeVar_list_branch : TypeVar.HasTypeVarEx with type t = branch list
  = TypeVar.HasTypeVar_list(HasTypeVar_branch)

and HasTypeVar_expr : TypeVar.HasTypeVarEx with type t = expr = struct
  type t = expr
  let rec substitute sub = function
    | Lam(tnames, eff, expr) -> Lam (HasTypeVar_list_tname.substitute sub tnames,
                                     TypeVar.HasTypeVar_typ.substitute sub eff,
                                     substitute sub expr)
    | Var{var_name=tname; var_info=info} -> Var{var_name=HasTypeVar_tname.substitute sub tname; var_info=info}
    | App(f, args) -> App(substitute sub f, HasTypeVar_list_expr.substitute sub args)
    | TypeLam(tvs, expr) ->
        let sub' = TypeVar.sub_remove tvs sub in
        TypeLam(tvs, HasTypeVar_expr.(sub' |-> expr))
    | TypeApp(expr, tps) -> TypeApp(substitute sub expr, TypeVar.HasTypeVar_list_typ.substitute sub tps)
    | Constructor{con_name=tname; con_repr=repr} -> Constructor{con_name=HasTypeVar_tname.substitute sub tname; con_repr=repr}
    | Literal lit -> Literal lit
    | Let(defgroups, expr) -> Let(HasTypeVar_list_defgroup.substitute sub defgroups, substitute sub expr)
    | Case c -> Case{case_exprs = HasTypeVar_list_expr.substitute sub c.case_exprs;
                     case_branches = HasTypeVar_list_branch.substitute sub c.case_branches}
                  
  let rec ftv = function
    | Lam(tnames, eff, expr) -> TypeVar.tvs_unions [HasTypeVar_list_tname.ftv tnames;
                                                    TypeVar.HasTypeVar_typ.ftv eff;
                                                    ftv expr]
    | Var v -> HasTypeVar_tname.ftv v.var_name
    | App(f, args) -> TypeVar.tvs_union (ftv f) (HasTypeVar_list_expr.ftv args)
    | TypeLam(tvs, expr) -> TypeVar.tvs_remove tvs (ftv expr)
    | TypeApp(expr, tps) -> TypeVar.tvs_union (ftv expr) (TypeVar.HasTypeVar_list_typ.ftv tps)
    | Constructor c -> HasTypeVar_tname.ftv c.con_name
    | Literal _ -> TypeVar.tvs_empty
    | Let(defgroups, expr) -> TypeVar.tvs_union (HasTypeVar_list_defgroup.ftv defgroups) (ftv expr)
    | Case c -> TypeVar.tvs_union (HasTypeVar_list_expr.ftv c.case_exprs) (HasTypeVar_list_branch.ftv c.case_branches)

  let rec btv = function
    | Lam(tnames, eff, expr) -> TypeVar.tvs_unions [HasTypeVar_list_tname.btv tnames;
                                                    TypeVar.HasTypeVar_typ.btv eff;
                                                    btv expr]
    | Var v -> HasTypeVar_tname.btv v.var_name
    | App(f, args) -> TypeVar.tvs_union (btv f) (HasTypeVar_list_expr.btv args)
    | TypeLam(tvs, expr) -> TypeVar.tvs_insert_all tvs (btv expr) (* The magic *)
    | TypeApp(expr, tps) -> TypeVar.tvs_union (btv expr) (TypeVar.HasTypeVar_list_typ.btv tps)
    | Constructor c -> HasTypeVar_tname.btv c.con_name
    | Literal _ -> TypeVar.tvs_empty
    | Let(defgroups, expr) -> TypeVar.tvs_union (HasTypeVar_list_defgroup.btv defgroups) (btv expr)
    | Case c -> TypeVar.tvs_union (HasTypeVar_list_expr.btv c.case_exprs) (HasTypeVar_list_branch.btv c.case_branches)
  
  let (|->) sub x = if TypeVar.sub_is_null sub then x else substitute sub x
end
and HasTypeVar_list_expr : TypeVar.HasTypeVarEx with type t = expr list = TypeVar.HasTypeVar_list(HasTypeVar_expr)
