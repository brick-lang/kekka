open Core

let explode s =
  let rec expl i l =
    if i < 0 then l else
      expl (i - 1) (s.[i] :: l) in
  expl (String.length s - 1) [];;


let name_system_core = Name.create "std/core"
let name_core = Name.create "core"
let prelude_name s =
  Name.qualify name_system_core @@ Name.create s;;

(* Special *)
let name_expr = Name.create ".expr"
let name_type = Name.create ".type"
let name_interactive_module = Name.create "interactive"
let name_interactive = Name.create "interactive"
let name_main = Name.create "main"
let name_copy = Name.create ".copy"
let name_op_expr = Name.create ".opexpr"

(* Primitive operations *)
let name_if = Name.create "if"
let name_case = Name.create "case"
let name_unit = Name.create "()"
let name_pred_heap_div = prelude_name "hdiv"
let name_return = prelude_name ".return"
let name_trace = prelude_name "trace"
let name_log = prelude_name "log"
let name_effect_open = Name.create ".open"
                   
(* Primitive constructors *)
let name_true = prelude_name "True"
let name_false = prelude_name "False"
                   
let name_just = prelude_name "Just"
let name_nothing = prelude_name "Nothing"
                     
let name_optional = prelude_name "Optional"
let name_optional_none = prelude_name "None"
let name_tp_optional = prelude_name "optional"

(* Lists *)
let name_null = prelude_name "Nil"
let name_cons = prelude_name "Cons"
let name_enum_from_to = prelude_name "enumFromTo"
let name_enum_from_then_to = prelude_name "enumFromThenTo"
let name_tp_list = prelude_name "list"

(* Primitive type constructors *)
let name_effect_empty = prelude_name "<>"
let name_effect_extend = prelude_name "<|>"
let name_effect_append = Name.create ".<+>"

let name_tp_bool    = prelude_name "bool"
let name_tp_int     = prelude_name "int"
let name_tp_float   = prelude_name "double"
let name_tp_char    = prelude_name "char"
let name_tp_string  = prelude_name "string"
let name_tp_any     = prelude_name "any"

let name_tp_io      = prelude_name "io"
let name_tp_unit    = prelude_name "()"
let name_tp_ref     = prelude_name "ref"
let name_ref        = prelude_name "ref"

let name_tp_total   = prelude_name "total"
let name_tp_partial = prelude_name "exn"
let name_tp_div     = prelude_name "div"
let name_tp_pure    = prelude_name "pure"

let name_tp_alloc   = prelude_name "alloc"
let name_tp_read    = prelude_name "read"
let name_tp_write   = prelude_name "write"
let name_tp_st      = prelude_name "st"

let name_tp_void    = prelude_name "void"

let name_tp_async   = prelude_name "async"
let name_tp_exception = prelude_name "exception"


let name_tuple n = prelude_name ("(" ^ String.make (n - 1) ',' ^ ")")

let is_name_tuple (name : Name.t) =
  let s = String.to_list name.Name.name_id in
  (name.Name.name_module) = (name_system_core.Name.name_id) &&
  (List.length s) >= 2 &&
  (List.hd_exn s) = '(' && (List.last_exn s) = ')' &&
  List.for_all ~f:((=) ',') (List.tl_exn (List.rev (List.tl_exn (List.rev s))))


(* Primitive kind constructors *)
let kind_star = Name.create "V"
let kind_label = Name.create "X"
let kind_fun = Name.create "->"
let kind_pred = Name.create "P"
let kind_effect = Name.create "E"
let kind_heap = Name.create "H"

