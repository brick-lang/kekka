(**
 * Definitions of kinds and helper functions
 * For more information, see Figure 1. of the paper.
*)

open Core
open Common

(** Kind constant *)
module KindCon = struct
  type t = Name.t
  let equal = Name.equal
  let show = Name.show
  let pp = Name.pp
  let t_of_sexp = Name.t_of_sexp
  let sexp_of_t = Name.sexp_of_t
end

(** Kinds *)
type t =
  | KCon of KindCon.t     (* kind constants "*", "->","!", "H", "P" *)
  | KApp of t * t         (* Application (only allowed for functions as yet) *)
[@@deriving eq,show,sexp]

(* let sexp_of_kind kind = 
 *   let open Sexplib in
 *   let ss = sexp_of_string in
 *   let sn = Name.sexp_of_t in
 *   let rec sk = function
 *     | KCon kc     -> sexp_of_pair ss sn ("KCon", kc)
 *     | KApp(k1,k2) -> Conv.sexp_of_triple ss sk sk ("KApp", k1, k2)
 *   in sk kind
 * 
 * let rec kind_of_sexp sexp =
 *   let open Sexp in
 *   match list_of_sexp Fn.id sexp with
 *   | [Atom "KCon"; kc]     -> KCon(Name.t_of_sexp kc)
 *   | [Atom "KApp"; k1; k2] -> KApp(kind_of_sexp k1, kind_of_sexp k2)
 *   | _ -> assert false           (\* TODO: Make this raise an exn *\) *)


(**
 * Kind and Type variables come in three flavours: 'Unifiable'
 * variables can be unified, 'Skolem' are non-unifiable (fresh)
 * variables, and 'Bound' variables are bound by a quantifier. *)
module Flavour = struct
  type t = Meta | Skolem | Bound
  [@@deriving show, sexp]
end

module Prim = struct 
  (* Kind @*@ *)
  let star = KCon Name.kind_star

  (* Kind @Label@ *)
  let label = KCon Name.kind_label

  (* Kind arrow @->@ *)
  let arrow = KCon Name.kind_fun

  let pred  = KCon Name.kind_pred

  let effect = KCon Name.kind_effect

  let heap = KCon Name.kind_heap

  (** Create a (kind) function from a kind to another kind *)
  let fun_1 k1 k2 = KApp(KApp(arrow, k1), k2)

  let arrow_n (n:int) =
    List.fold_right ~f:fun_1 ~init:(fun_1 effect star) @@
    List.init n ~f:(fun _ -> star)

  let extend = fun_1 label (fun_1 effect effect) (* label -> (effect -> effect) *)

  let is_kind_fun : t -> bool = function
    | KApp(KApp(k0,k1),k2) -> phys_equal (k0) (arrow)
    | _ -> false

  let rec extract_kind_fun : t -> (t list * t) = function
    | KApp(KApp(k0,k1),k2) when
        phys_equal k0 (arrow) ->
        let (args,res) = extract_kind_fun k2 in
        ((k1::args), res)

    | k -> ([],k)

  let is_star   (k:t) : bool = phys_equal k (star)
  let is_effect (k:t) : bool = phys_equal k (effect)

  let builtin_kinds : (Name.t * t) list =
    [
      (Name.kind_star, star); (* Value *)
      (Name.kind_fun, arrow); (* Type constructor *)
      (Name.kind_pred, pred); (* Predicate *)
      (Name.kind_effect, effect); (* Effect constants *)
      (Name.kind_label, label);   (* Labels *)
      (Name.kind_heap, heap) (* Heaps *)
    ]
end
