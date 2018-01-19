type t =
  | Var       of string         (* x *)
  | Primitive of primitive      (* p *)
  | Apply     of t * t          (* e1 e2 *)
  | Lambda    of string * t     (* λx.e *)
  | Let       of string * t * t (* let x = e1 in e2 *)
  | Catch     of t * t          (* catch e1 e2 *)
  | Run       of t              (* run e *)

and primitive = Unit | Fix | Throw | New | Bang | Assign

let prim_to_string = function
  | Unit   -> "()"
  | Fix    -> "fix"
  | Throw  -> "throw"
  | New    -> "new"
  | Bang   -> "(!)"
  | Assign -> "(:=)"

let rec to_string = function
  | Var(v)       -> v
  | Primitive(p) -> prim_to_string p
  | Apply(f,a)   -> Printf.sprintf "(%s %s)" (to_string f) (to_string a)
  | Lambda(a,b)  -> Printf.sprintf "(fun %s -> %s)" a (to_string b)
  | Let(v,e,b)   -> Printf.sprintf "(let %s = %s in %s)" v (to_string e) (to_string b)
  | Catch(ex,b)  -> Printf.sprintf "(catch %s %s)" (to_string ex) (to_string b)
  | Run(e)       -> Printf.sprintf "(run %s)" (to_string e)


