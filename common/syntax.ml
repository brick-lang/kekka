(* Common syntactical constructs *)


(*******************************
   Backend targets
 ********************************)

module Target = struct
  type t = CS | JS | Default
  [@@deriving eq, ord]

  let show = function
    | CS -> "cs"
    | JS -> "js"
    | Default -> ""
end

module Host = struct
  type t = Node | Browser

  let show = function
    | Node -> "node"
    | Browser -> "browser"
end

(*********************************
   Visibility
 *********************************)
module Visibility = struct 
  type t = Public | Private
  [@@deriving eq, ord, show]

  let is_public = function
    | Public -> true
    | _ -> false

  let is_private = function
    | Private -> true
    | _ -> false
end

(************************************
   Data Kind
 ************************************)
module DataKind = struct 
  type t = Inductive | CoInductive | Retractive
  [@@deriving eq]
  
  let show = function
    | Inductive -> "type"
    | CoInductive -> "cotype"
    | Retractive -> "rectype"

  let pp fmt dk = Format.pp_print_string fmt (show dk)
end

(************************************
   Definition Kind
 ************************************)

module DefSort = struct
  type t = Fun | Val | Var
  [@@deriving eq, ord]
  
  let show = function
    | Fun -> "fun"
    | Val -> "val"
    | Var -> "var"
end

(*************************************
   Fixities
 *************************************)
(** Operator associativity *)
module Assoc = struct 
  type t = None | Right | Left
  [@@deriving eq, show]
end

(** Operator fixity *)
module Fixity = struct 
  type t = 
    | Infix of int * Assoc.t  (* precedence and associativity  *)
        [@equal fun (i1,a1) (i2,a2) -> (i1 = i2) && (Assoc.equal a1 a2)]
    | Prefix
    | Postfix
  [@@deriving show, eq]
end

