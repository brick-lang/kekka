
let expr = Name.create ".expr";;
let typ = Name.create ".type";;
let interactive_module = Name.create "interactive";;


(* Primitive kind constructors *)
let kind_star = Name.create "V"
let kind_label = Name.create "X"
let kind_fun = Name.create "->"
let kind_pred = Name.create "P"
let kind_effect = Name.create "E"
let kind_heap = Name.create "H"
