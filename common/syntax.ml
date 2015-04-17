

(* 
   Common syntactical constructsn
 *)


(*******************************
   Backend targets
 ********************************)

type target = CS | JS | Default [@@deriving eq, ord]

let show_target = function
  | CS -> "cs"
  | JS -> "js"
  | Default -> ""

type host = Node | Browser [@@deriving eq, ord]

let show_host = function
  | Node -> "node"
  | Browser -> "browser"

(*********************************
   Visibility
 *********************************)

type visibility = Public | Private [@@deriving eq,ord,show]

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
                   [@@deriving eq]

let show_data_kind = function
  | Inductive -> "type"
  | CoInductive -> "cotype"
  | Retractive -> "rectype"

let pp_data_kind fmt dk = Format.pp_print_string fmt (show_data_kind dk)

(************************************
   Definition Kind
 ************************************)

type def_sort = DefFun | DefVal | DefVar
                  [@@deriving eq,ord]

let show_def_sort = function
  | DefFun -> "fun"
  | DefVal -> "val"
  | DefVar -> "var"

(*************************************
   Fixities
 *************************************)

(** Operator associativity *)
type assoc = AssocNone
           | AssocRight
           | AssocLeft
               [@@deriving eq,show]

(** Operator fixity *)
type fixity = FixInfix of int * assoc (** precedence and associativity  *)
            | FixPrefix
            | FixPostfix
                [@@deriving eq,show]
