
let assertwith msg test x =
  if test then x else failwith msg

let todo msg =
  failwith ("todo: " ^ msg)

let match_fail msg =
  failwith ("unmatched pattern: " ^ msg)
