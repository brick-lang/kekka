open Id
(* module type HasUnique = sig *)
(*   type 'a m *)
(*   val update_unique: (int -> int) -> int m *)
(*   val set_unique: int -> unit m *)
(*   val unique: int m *)
(*   val uniques: int -> (int list) m *)
(*   val unique_id : string -> id m *)
(*   val unique_ids : string -> int -> id list m *)
(*   val unique_names : string -> name m *)
(* end *)

type 'a unique = int -> ('a * int)

(** Run a unique monad, starting with an initial unique seed *)
let run_unique (i:int) (u:'a unique) : ('a * int) = u i

(** Run a unique monad that will generate unique identifiers
  * with respect to a given set of identifiers *)
let run_unique_with (ids:Id.t list) (uniq:'a unique) : 'a =
  let seed = (List.fold_right ~f:max ~init:0 (List.map ~f:Id.number ids)) + 1 in
  fst @@ run_unique seed uniq

let lift_unique {H:HasUnique} (uniq:'a unique) : 'a H.t =
  unique >>= fun u ->
  let (x,u') = run_unique u uniq in
  set_unique u' >>
  return x
    
