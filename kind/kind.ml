
(**
 * Definitions of kinds and helper functions
 * For more information, see Figure 1. of the paper.
*)


open Core
open Common


(** Kind constant *)
type kind_con = Name.name

(* implicit *)
module Eq_kind_con : BasicClasses.Eq with type t = kind_con = struct
  type t = kind_con
  let equal x y = Name.Eq_name.equal x y
end

(* implicit *)
module Show_kind_con = struct
  type t = kind_con
  let show kc = Name.show_name kc
end

(** Kinds *)
type kind =
  | KCon of kind_con      (* kind constants "*", "->","!", "H", "P" *)
  | KApp of kind * kind   (* Application (only allowed for functions as yet) *)

(* implicit *)
module Eq_kind : BasicClasses.Eq with type t = kind = struct
  type t = kind
  let equal x y =
    let rec equal' x y = match x with
      | KCon kc1 -> (match y with
          | KCon kc2 -> Eq_kind_con.equal kc1 kc2
          | _ -> false)
      | KApp (k1,k2) -> (match y with
          | KApp (k'1, k'2) -> (equal' k1 k'1) &&
                               (equal' k2 k'2)
          | _ -> false)
    in equal' x y
end

(* implicit *)
module Show_kind = struct
  type t = kind
  let show k =
    let rec show' = function
      | KCon kc -> Printf.sprintf "KindCon %s" (Show_kind_con.show kc)
      | KApp (k1,k2) -> Printf.sprintf "KindApp (%s,%s)" (show' k1) (show' k2)
    in show' k
end

let sexp_of_kind kind = 
  let open Sexplib in
  let ss = sexp_of_string in
  let sn = Name.sexp_of_name in
  let rec sk = function
    | KCon kc     -> sexp_of_pair ss sn ("KCon", kc)
    | KApp(k1,k2) -> Conv.sexp_of_triple ss sk sk ("KApp", k1, k2)
  in sk kind

let rec kind_of_sexp sexp =
  let open Sexp in
  match list_of_sexp Fn.id sexp with
  | [Atom "KCon"; kc]     -> KCon(Name.name_of_sexp kc)
  | [Atom "KApp"; k1; k2] -> KApp(kind_of_sexp k1, kind_of_sexp k2)
  | _ -> assert false           (* TODO: Make this raise an exn *)


(**
 * Kind and Type variables come in three flavours: 'Unifiable'
 * variables can be unified, 'Skolem' are non-unifiable (fresh)
 * variables, and 'Bound' variables are bound by a quantifier. *)
type flavour = 
  | Bound
  | Skolem
  | Meta

(* implicit *)
module Show_flavour = struct
  type t = flavour
  let show = function
    | Bound  -> "Bound"
    | Skolem -> "Skolem"
    | Meta   -> "Meta"
end  


let sexp_of_flavour = function
  | Bound  -> Sexp.Atom "Bound"
  | Skolem -> Sexp.Atom "Skolem"
  | Meta   -> Sexp.Atom "Meta"

let flavour_of_sexp =
  let open Sexp in function
    | Atom "Bound"  -> Bound
    | Atom "Skolem" -> Skolem
    | Atom "Meta"   -> Meta
    | _             -> assert false (* TODO: make this raise an exn *)

(* Kind @*@ *)
let kind_star   : kind = KCon Name_prim.kind_star

(* Kind @Label@ *)
let kind_label  : kind = KCon Name_prim.kind_label

(* Kind arrow @->@ *)
let kind_arrow  : kind = KCon Name_prim.kind_fun

let kind_pred   : kind = KCon Name_prim.kind_pred

let kind_effect : kind = KCon Name_prim.kind_effect

let kind_heap   : kind = KCon Name_prim.kind_heap

(** Create a (kind) function from a kind to another kind *)
let kind_fun k1 k2 : kind = KApp(KApp(kind_arrow, k1), k2)

let kind_arrow_n (n:int) : kind =
  List.fold_right ~f:kind_fun ~init:(kind_fun kind_effect kind_star) @@
  List.init n ~f:(fun _ -> kind_star)

let kind_extend : kind = kind_fun kind_label (kind_fun kind_effect kind_effect)

let is_kind_fun : kind -> bool = function
  | KApp(KApp(k0,k1),k2) -> phys_equal (k0) (kind_arrow)
  | _ -> false

let rec extract_kind_fun : kind -> (kind list * kind) = function
  | KApp(KApp(k0,k1),k2) when
      phys_equal k0 (kind_arrow) ->
      let (args,res) = extract_kind_fun k2 in
      ((k1::args), res)

  | k -> ([],k)


let is_kind_star   (k:kind) : bool = phys_equal k (kind_star)
let is_kind_effect (k:kind) : bool = phys_equal k (kind_effect)

let builtin_kinds : (Name.name * kind) list =
  [
    (Name_prim.kind_star, kind_star); (* Value *)
    (Name_prim.kind_fun, kind_arrow); (* Type constructor *)
    (Name_prim.kind_pred, kind_pred);
    (Name_prim.kind_effect, kind_effect); (* Effect constants *)
    (Name_prim.kind_label, kind_label);
    (Name_prim.kind_heap, kind_heap) (* Heaps *)
  ]

