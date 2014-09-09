open Name

(* Kinds *)
type kind =
  | KCon of kind_con               (* kind constants "*", "->","!", "H", "P" *)
  | KApp of kind * kind              (* Application (only allowed for functions as yet) *)

(* kind constant *)
and kind_con = name

(**
 * kind and type variables come in three flavours: 'Unifiable'
 * variables can be unified, 'Skolem' are non-unifiable (fresh)
 * variables, and 'Bound' variables are bound by a quantifier. *)
type flavour = 
  | Bound
  | Skolem
  | Meta
with sexp

(* Kind @*@ *)
let kind_star = KCon Name_prim.kind_star;;
