open Core
open Common

(** Inference Kind: These kinds contain meta kind-variables *)
module InfKind = struct
  type t =
    | Var of Common.Id.t         (* variable *)
    | Con of Heart.Kind.t     (* constant *)
    | App of t * t               (* application *)

  let star = Con Heart.Kind.Prim.star
  (* let inf_kind_handled = KICon Kind.kind_handled *)
  let fun_1 k1 k2 = App(App(Con Heart.Kind.Prim.arrow, k1), k2) (* (->) k1 k2 *)
  let fun_n kinds k = List.fold_right ~init:k ~f:fun_1 kinds

  (* HasKindVar *)
  let rec (|=>) sub kind = match kind with 
    | Var id      -> (match Id.Map.find sub id with Some k -> k | None -> kind)
    | Con _       -> kind
    | App (k1,k2) -> App (sub |=> k1, sub |=> k2)
  let rec fkv = function
    | Var id      -> Id.Set.singleton id
    | Con _       -> Id.Set.empty
    | App (k1,k2) -> Id.Set.union (fkv k1) (fkv k2)
end

module InfKGamma = struct
  type t = InfKind.t Common.Name.Map.t
end


(**************************************************************
 * Substitution 
 **************************************************************)
open Util

(* module HasKindVar_list(H:HasKindVar) : HasKindVar with type t = H.t list = struct
 *   type t = H.t list
 *   let (|=>) sub = List.map ~f:(H.(|=>) sub)
 *   let fkv = Id.Set.union_list <.> List.map ~f:H.fkv
 * end
 * 
 * module HasKindVar_list_inf_kind = HasKindVar_list(InfKind) *)
module KVs = struct
  type t  = Id.Set.t
  let member = Util.flip Id.Set.mem
  let list = Id.Set.to_list
end

module KSub = struct
  type t = InfKind.t Id.Map.t

  let empty = Id.Map.empty
  let single id kind = Id.Map.singleton id kind

  (* Left-biased union *)
  let union m1 m2 = Id.Map.merge m1 m2 ~f:(fun ~key ->
      function `Both(l,r) -> Some l | `Left l -> Some l | `Right r -> Some r)

  (* HasKindVar *)
  let (|=>) sub ksub = Id.Map.map ~f:(InfKind.(|=>) sub) ksub
  let fkv (sub:t) : KVs.t = Id.Map.data sub |> List.map ~f:InfKind.fkv |> Id.Set.union_list

  (* Assumes a left-biased union (which it is) *)
  let (@@@) sub1 sub2 = union sub1 (sub1 |=> sub2)
end

module type HasKindVar = sig
  type t
  val (|=>) : KSub.t -> t -> t
  val fkv : t -> KVs.t
end


(**************************************************************
 * Precedence
 **************************************************************)
module Prec = struct
  type t = Int.t
  let top   = 0
  let arrow = 1
  let app   = 2
  let atom  = 3
end
(* let pparens ctxt prec doc = if ctxt >= prec then parens doc else doc *)
