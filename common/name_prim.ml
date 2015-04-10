
(* Special *)
let expr = Name.create ".expr"
let typ = Name.create ".type"
let interactive_module = Name.create "interactive"
let interactive = Name.create "interactive"
let main = Name.create "main"
let copy = Name.create ".copy"
let op_expr = Name.create ".opexpr"

(* Primitive operations *)
let name_if = Name.create "if"
let case = Name.create "case"
let unit = Name.create "()"

let pred_heap_div : Name.name = Name.prelude_name "hdiv"


(* Primitive kind constructors *)
let kind_star = Name.create "V"
let kind_label = Name.create "X"
let kind_fun = Name.create "->"
let kind_pred = Name.create "P"
let kind_effect = Name.create "E"
let kind_heap = Name.create "H"

