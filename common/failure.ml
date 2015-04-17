


let failure msg =
  raise (Failure("*** Internal compiler error: " ^ msg))

let assertion msg test x =
  if test then x else failure msg

let todo msg =
  failure "todo: " ^ msg

let match_failure msg =
  failure "unmatched pattern: " ^ msg
