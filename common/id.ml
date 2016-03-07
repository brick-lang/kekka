open Core.Std;;

(* Types *)

(** Identifiers are unique compiler generated identities *)
type id = int

(** A list of identifiers *)
type ids = id list
	   
(** show quotes around the id *)
let rec pp_id fmt id =
  Format.pp_print_string fmt @@ "\"" ^ (Int.to_string id) ^ "\""
				
(** create a fresh identifier *)
let create i = i

let create_from_id id = id + 1
			
(** Generate an 'Id' with a certain base name (which is ignored) :)  *)
let generate base_name = create

(* dummy identifier *)
let nil : id = 0

let number i = i

let show_id = string_of_int
let sexp_of_id = sexp_of_int
let id_of_sexp = int_of_sexp
