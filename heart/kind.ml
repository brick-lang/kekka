(**
 * Definitions of kinds and helper functions
 * For more information, see Figure 1. of the paper.
*)

open Core
open Common

(** Kinds *)
type t =
  | Constant of Name.t     (* kind constants "*", "->","!", "H", "P" *)
  | App      of t * t      (* Application (only allowed for functions as yet) *)
[@@deriving eq,show,sexp]

(**
 * Kind and Type variables come in three flavours: 'Unifiable'
 * variables can be unified, 'Skolem' are non-unifiable (fresh)
 * variables, and 'Bound' variables are bound by a quantifier. *)
module Flavour = struct
  type t = Meta | Skolem | Bound
  [@@deriving show,eq,ord,sexp]
end

module Prim = struct 
  (* Kind @*@ *)
  let star = Constant Name.kind_star

  (* Kind @Label@ *)
  let label = Constant Name.kind_label

  (* Kind arrow @->@ *)
  let arrow = Constant Name.kind_fun

  let pred  = Constant Name.kind_pred

  let effect = Constant Name.kind_effect

  let heap = Constant Name.kind_heap

  (** Create a (kind) function from a kind to another kind *)
  let fun_1 k1 k2 = App(App(arrow, k1), k2)

  let arrow_n (n:int) =
    List.fold_right ~f:fun_1 ~init:(fun_1 effect star) @@
    List.init n ~f:(fun _ -> star)

  let extend = fun_1 label (fun_1 effect effect) (* label -> (effect -> effect) *)
end

let is_kind_fun : t -> bool = function
  | App(App(k0,k1),k2) -> phys_equal (k0) (Prim.arrow)
  | _ -> false

let rec extract_kind_fun : t -> (t list * t) = function
  | App(App(k0,k1),k2) when
      phys_equal k0 (Prim.arrow) ->
      let (args,res) = extract_kind_fun k2 in
      ((k1::args), res)

  | k -> ([],k)

let is_star   (k:t) : bool = phys_equal k (Prim.star)
let is_effect (k:t) : bool = phys_equal k (Prim.effect)

let builtin_kinds : (Name.t * t) list =
  [
    (Name.kind_star,   Prim.star);   (* Value *)
    (Name.kind_fun,    Prim.arrow);  (* Type constructor *)
    (Name.kind_pred,   Prim.pred);   (* Predicate *)
    (Name.kind_effect, Prim.effect); (* Effect constants *)
    (Name.kind_label,  Prim.label);  (* Labels *)
    (Name.kind_heap,   Prim.heap)    (* Heaps *)
  ]

