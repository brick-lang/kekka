open Core

(* Types *)

(** Identifiers are unique compiler generated identities *)
type t = int

(** A list of identifiers *)
type ids = t list

(** show quotes around the id *)
let rec pp_id fmt id =
  Format.pp_print_string fmt @@ "\"" ^ (Int.to_string id) ^ "\""

(** create a fresh identifier *)
let create (i:int) : t = i

let create_from_id (id:t) : t = id + 1

(** Generate an 'Id' with a certain base name (which is ignored) :)  *)
let generate base_name (id:t) = create id

(* dummy identifier *)
let nil : t = 0

let number (i:t) : int = i

let sexp_of_t : t -> Sexp.t = sexp_of_int
let t_of_sexp : Sexp.t -> t = int_of_sexp

let show (i:t) = string_of_int i

module Map = Int.Map
module Set = Int.Set
