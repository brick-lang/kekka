open Core.Std;;

(* Types *)

(* A list of identifiers *)
type ids = id list
(* Identifiers are unique compiler generated identities *)
and id = int

(* show quotes around the id *)
let rec to_string id =
  "\"" ^ (Int.to_string id) ^ "\""

and generate base_name i = 
  create i

(* create a fresh identifier *)
and create i = i

and create_from_id id = id + 1

(* dummy identifier *)
and nil: id = 0

and number i = i
