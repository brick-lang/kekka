
open BasicClasses

(* 
   Common syntactical constructsn
 *)
 
 
(*******************************
   Backend targets
 ********************************)

type target = CS | JS | Default

implicit 
module Eq_target = struct
  type t = target
  let equal x y = match x with
    | CS -> (match y with
        | CS -> true
        | _ -> false)
    | JS -> (match y with
        | JS -> true
        | _ -> false)
    | Default -> (match y with
        | Default -> true
        | _ -> false)
end

implicit 
module Ord_target = struct
  type t = target
  module Eq = Eq_target
  let compare x y = match x with
    | CS -> (match y with
        | CS -> 0
        | _ -> 1)
    | JS -> (match y with
        | CS -> -1
        | JS -> 0
        | Default -> 1)
    | Default -> (match y with
        | Default -> 0
        | _ -> -1)
end
  
implicit 
module Show_target = struct
  type t = target
  let show = function
    | CS -> "cs"
    | JS -> "js"
    | Default -> ""
end
    
type host = Node | Browser

let show_host = function
  | Node -> "node"
  | Browser -> "browser"
  
(*********************************
   Visibility
 *********************************)

type visibility = Public | Private

implicit 
module Eq_visibility = struct
  type t = visibility
  let equal x y = match x with
    | Public -> (match y with
        | Public -> true
        | Private -> false)
    | Private -> (match y with
        | Public -> false
        | Private -> true)
end

implicit 
module Ord_visibility = struct
  type t = visibility
  module Eq = Eq_visibility
  let equal x y = match x with
    | Public -> (match y with
        | Public -> 0
        | Private -> 1)
    | Private -> (match y with
        | Public -> -1
        | Private -> 0)
end

implicit 
module Show_visibilty = struct
  type t = visibility
  let show = function
    | Public -> "Public"
    | Private -> "Private"
end

let is_public = function
  | Public -> true
  | _ -> false
  
let is_private = function
  | Private -> true
  | _ -> false
  
(************************************
   Data Kind
 ************************************)

type data_kind = Inductive | CoInductive | Retractive

implicit
module Eq_data_kind = struct
  type t = data_kind
  let equal x y = match x with
    | Inductive -> (match y with
        | Inductive -> true
        | _ -> false)
    | CoInductive -> (match y with
        | CoInductive -> true
        | _ -> false)
    | Retractive -> (match y with
        | Retractive -> true
        | _ -> false)
      
end
  
implicit
module Show_data_kind = struct
  type t = data_kind
  let show = function
    | Inductive -> "type"
    | CoInductive -> "cotype"
    | Retractive -> "rectype"
end
  
let pp_data_kind fmt dk = Format.pp_print_string fmt (Show_data_kind.show dk)
						     
(************************************
   Definition Kind
 ************************************)

type def_sort = DefFun | DefVal | DefVar

  
implicit 
module Eq_def_sort = struct
  type t = def_sort
  let equal x y = match x with
    | DefFun -> (match y with
        | DefFun -> true
        | _ -> false)
    | DefVal -> (match y with
        | DefVal -> true
        | _ -> false)
    | DefVar -> (match y with
        | DefVar -> true
        | _ -> false)
end

implicit 
module Ord_def_sort = struct
  type t = def_sort
  module Eq = Eq_def_sort
  let compare x y = match x with
    | DefFun -> (match y with
        | DefFun -> 0
        | _ -> 1)
    | DefVal -> (match y with
        | DefFun -> -1
        | DefVal -> 0
        | DefVar -> 1)
    | DefVar -> (match y with
        | DefVar -> 0
        | _ -> -1)
end

implicit
module Show_def_sort = struct
  type t = def_sort
  let show = function
    | DefFun -> "fun"
    | DefVal -> "val"
    | DefVar -> "var"
end
    
(*************************************
   Fixities
 *************************************)

(** Operator associativity *)
type assoc = AssocNone
           | AssocRight
           | AssocLeft

implicit
module Eq_assoc = struct
  type t = assoc
  let equal x y = match x with
    | AssocNone -> (match y with
        | AssocNone -> true
        | _ -> false)
    | AssocRight -> (match y with
        | AssocRight -> true
        | _ -> false)
    | AssocLeft -> (match y with
        | AssocLeft -> true
        | _ -> false)
end

implicit
module Show_assoc = struct
  type t = assoc
  let show = function
    | AssocNone  -> "AssocNone"
    | AssocRight -> "AssocRight"
    | AssocLeft  -> "AssocLeft"
end

  
(** Operator fixity *)
type fixity = FixInfix of int * assoc (** precedence and associativity  *)
            | FixPrefix
            | FixPostfix

implicit
module Eq_fixity = struct
  type t = fixity
  let equal x y = match x with
    | FixInfix (i1,a1) -> (match y with
        | FixInfix (i2,a2) -> 
            (i1 = i2) &&
            (Eq_assoc.equal a1 a2)
        | _ -> false)
    | FixPrefix -> (match y with
        | FixPrefix -> true
        | _ -> false)
    | FixPostfix -> (match y with
        | FixPostfix -> true
        | _ -> false)
end

implicit
module Show_fixity = struct
  type t = fixity
  let show = function
    | FixInfix (_,_) -> "FixInfix"
    | FixPrefix      -> "FixPrefix"
    | FixPostfix     -> "FixPostfix"
end

