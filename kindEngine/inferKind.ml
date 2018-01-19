open Core

(** Inference Kind: These kinds contain meta kind-variables *)
type inf_kind =
  | KIVar of Common.Id.id        (* variable *)
  | KICon of Inner.kind          (* constructor *)
  | KIApp of inf_kind * inf_kind (* application *)

type inf_kgamma = inf_kind Common.Name.Map.t

let inf_kind_star = KICon Inner.kind_star
(* let inf_kind_handled = KICon Kind.kind_handled *)
let inf_kind_fun k1 k2 = KIApp( KIApp(KICon Inner.kind_arrow, k1), k2) (* (->) k1 k2 *)
let inf_kind_fun_n kinds k = List.fold_right ~init:k ~f:inf_kind_fun kinds

(**************************************************************
 * Substitution 
 **************************************************************)
open Common
open Util
    
type ksub = inf_kind Id.Map.t
type kvs  = Id.Set.t

let ksub_empty = Id.Map.empty
let ksub_single id kind = Id.Map.singleton id kind

let kvs_member = Util.flip Id.Set.mem
let kvs_list = Id.Set.to_list

module type HasKindVar = sig
  type t
  val (|=>) : ksub -> t -> t
  val fkv : t -> kvs
end

module HasKindVar_inf_kind : HasKindVar with type t = inf_kind = struct
  type t = inf_kind
  let rec (|=>) sub kind = match kind with 
    | KIVar id      -> (match Id.Map.find sub id with Some k -> k | None -> kind)
    | KICon _       -> kind
    | KIApp (k1,k2) -> KIApp (sub |=> k1, sub |=> k2)
  let rec fkv = function
    | KIVar id      -> Id.Set.singleton id
    | KICon _       -> Id.Set.empty
    | KIApp (k1,k2) -> Id.Set.union (fkv k1) (fkv k2)
end

module HasKindVar_list(H:HasKindVar) : HasKindVar with type t = H.t list = struct
  type t = H.t list
  let (|=>) sub = List.map ~f:(H.(|=>) sub)
  let fkv = Id.Set.union_list <.> List.map ~f:H.fkv
end

module HasKindVar_list_inf_kind = HasKindVar_list(HasKindVar_inf_kind)

module HasKindVar_ksub : HasKindVar with type t = ksub = struct
  type t = ksub
  let (|=>) sub ksub = Id.Map.map ~f:(HasKindVar_inf_kind.(|=>) sub) ksub
  let fkv = HasKindVar_list_inf_kind.fkv <.> Id.Map.data
end

(* Left-biased union *)
let ksub_union m1 m2 =
  List.fold_left ~init:m2 ~f:(fun m (k,v) -> Id.Map.add m ~key:k ~data:v) (Id.Map.to_alist m1)

(* Assumes a left-biased union (which it is) *)
let (@@@) sub1 sub2 = ksub_union sub1 HasKindVar_ksub.(sub1 |=> sub2)


(**************************************************************
 * Precedence
 **************************************************************)
type prec = Int.t
let prec_top   = 0
let prec_arrow = 1
let prec_app   = 2
let prec_atom  = 3

(* let pparens ctxt prec doc = if ctxt >= prec then parens doc else doc *)
