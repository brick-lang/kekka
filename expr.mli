type t =
  | Var       of string
  | Primitive of primitive
  | Apply     of t * t
  | Lambda    of string * t
  | Let       of string * t * t
  | Catch     of t * t
  | Run       of t
and primitive = Unit | Fix | Throw | New | Bang | Assign
val to_string : t -> string
