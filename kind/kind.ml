
(**
 * Definitions of kinds and helper functions
 *)


open Name
open Core.Std


(** Kind constant *)
type kind_con = name

(** Kinds *)
type kind =
  | KCon of kind_con      (* kind constants "*", "->","!", "H", "P" *)
  | KApp of kind * kind   (* Application (only allowed for functions as yet) *)

(**
 * Kind and Type variables come in three flavours: 'Unifiable'
 * variables can be unified, 'Skolem' are non-unifiable (fresh)
 * variables, and 'Bound' variables are bound by a quantifier. *)
type flavour = 
  | Bound
  | Skolem
  | Meta
with sexp

(* Kind @*@ *)
let kind_star = KCon Name_prim.kind_star

(* Kind @Label@ *)
let kind_label = KCon Name_prim.kind_label

(* Kind arrow @->@ *)
let kind_arrow = KCon Name_prim.kind_fun

let kind_pred = KCon Name_prim.kind_pred

let kind_effect = KCon Name_prim.kind_effect

let kind_heap = KCon Name_prim.kind_heap

(** Create a (kind) function from a kind to another kind *)
let kind_fun k1 k2 : kind =
  KApp(KApp(kind_arrow, k1), k2)

let kind_arrow_n (n:int) : kind =
  List.fold_right ~f:kind_fun ~init:(kind_fun kind_effect kind_star) @@ List.init n ~f:(fun _ -> kind_star)

let kind_extend = kind_fun kind_label (kind_fun kind_effect kind_effect)

let is_kind_fun = function
  | KApp(KApp(k0,k1),k2) -> phys_equal (k0) (kind_arrow)
  | _ -> false
;;

let rec extract_kind_fun = function
  | KApp(KApp(k0,k1),k2) when
      phys_equal k0 (kind_arrow) ->
    let (args,res) = extract_kind_fun k2 in
    ((k1::args), res)
    
  | k -> ([],k)
;;

let is_kind_star k = phys_equal k (kind_star)
let is_kind_effect k = phys_equal k (kind_effect)

let builtin_kinds : (name * kind) list =
  [
    (Name_prim.kind_star, kind_star);
    (Name_prim.kind_fun, kind_arrow);
    (Name_prim.kind_pred, kind_pred);
    (Name_prim.kind_effect, kind_effect);
    (Name_prim.kind_label, kind_label);
    (Name_prim.kind_heap, kind_heap)
  ]
