
module Expr = struct type 'a t end

(*****************************************************************
 * Definitions 
 *****************************************************************)

module ValueBinder = struct
  type ('t,'e) t = {
    name : Name.t;
    typ : 't;                   (* Type. Always present for constructors. *)
    expr : 'e;                  (* Expression: always present for definitions as 'Expr t' 
                                 * Function and constructor parameters use 'Maybe (Expr t)' for default values.
                                 * Pattern bindings ('PatVar') use unit '()'. *)
  }
end

(*****************************************************************
 * type definitions 
 *****************************************************************)

module TypeBinder = struct
  type 'a t = {
    name : Name.t;
    kind : 'a;
    (* name_range : Range.t;
     * range : Range.t; *)
  }
end

(** Constructor: name, existentials, type parameters, name range, total range, and visibility *)
module UserCon = struct
  type ('t,'u,'k) t = {
    name : Name.t;
    exists : 'k TypeBinder.t;
    params : (Syntax.Visibility.t * ('t, 'u Expr.t option) ValueBinder.t);
    vis : Syntax.Visibility.t;
    doc : string;
  }
end 

module TypeDef = struct
  type ('t,'u,'k) t =
    | Synonym of {
        binder : 'k TypeBinder.t;
        params : 'k TypeBinder.t list;
        synonym : 't;
        vis : Syntax.Visibility.t;
        doc : string;
      }

    | DataType of {
        binder : 'k TypeBinder.t;
        params : 'k TypeBinder.t list;
        constrs : ('t, 'u, 'k) UserCon.t;
        sort : Syntax.DataKind.t;
        def : Syntax.DataDef.t;
        vis : Syntax.Visibility.t;
        is_extend: bool;
        doc : string;
      }
  let is_extend = function DataType{is_extend=true} -> true | _ -> false
  let binder = function DataType{binder} | Synonym{binder} -> binder
  let is_datatype = function DataType _ -> true | _ -> false
  let is_synonym = function Synonym _ -> true | _ -> false
end 

module TypeDefGroup = struct
  type ('t,'k) t =
    | Rec    of ('t,'t,'k) TypeDef.t list
    | NonRec of ('t,'t,'k) TypeDef.t
end


(*****************************************************************
 * Types and Kinds
 *****************************************************************)
module UserQuantifier = struct
  type t = Some | Forall | Exists
  let show = function
    | Some -> "some"
    | Forall -> "forall"
    | Exists -> "exists"
end 

(** (Higher ranked) types *)
module KindedUserType = struct
  type 'k t =
    | Quan   of UserQuantifier.t * 'k TypeBinder.t * 'k t
    | Qual   of 'k t list * 'k t
    | Fun    of (Name.t * 'k t) list * 'k t * 'k t
    | App    of 'k t * 'k t list
    | Var    of Name.t
    | Con    of Name.t
    | Parens of 'k t
    | Ann    of 'k t * 'k
end

(** A kind *)
module UserKind = struct
  type t =
    | Con    of Name.t
    | Arrow  of t * t
    | Parens of t
    | None                      (* flags that there is no explicit kind annotation *)
end

module UserType = struct
  type t = UserKind.t KindedUserType.t
end 

(*****************************************************************
 * Core Program
 *****************************************************************)
module Program = struct
  type ('t,'k) t = {
    name : Name.t;
    typedefs : ('t, 'k) TypeDefGroup.t list;
  }
end 
