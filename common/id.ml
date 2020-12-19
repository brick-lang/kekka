open Core

(* Types *)

(** Identifiers are unique compiler generated identities *)
type t = int
[@@deriving show, sexp]

let equal = Int.equal
let compare = Int.compare

(** A list of identifiers *)
type ids = t list

(** show quotes around the id *)
let rec pp fmt id =
  Format.pp_print_string fmt @@ "\"" ^ (Int.to_string id) ^ "\""

(** create a fresh identifier *)
let create (i:int) : t = i

let create_from_id (id:t) : t = id + 1

(** Generate an 'Id' with a certain base name (which is ignored) :)  *)
let generate base_name (id:t) = create id

(* dummy identifier *)
let nil : t = 0

let number (i:t) : int = i

module Map = Int.Map
module Set = Int.Set
