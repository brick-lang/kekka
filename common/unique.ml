(* Instead of using a monad, I'll be using OCaml's global state/ref system. Like a hack. *)
let counter =
  let count = ref (-1) in
  fun () -> incr count; !count

open Core

let unique = counter
let uniques n = List.init n ~f:Util.id |> List.map ~f:(fun _ -> unique ())
let unique_id basename = Id.generate basename (unique ())
let unique_ids basename n = List.map ~f:(Id.generate basename) (uniques n)
let unique_name basename = Name.new_hidden_name (basename ^ "." ^ Int.to_string (unique ()))
