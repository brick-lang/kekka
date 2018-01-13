open Core
open Util
open Type
open TypeVar

(********************************************
 * Unify monad 
 ********************************************)
type unify_error =
  | NoMatch
  | NoMatchKind
  | NoMatchPred
  | NoSubsume
  | NoEntail
  | Infinite
  | NoArgMatch of int * int

type st = { uniq : int; sub : TypeVar.sub }
type 'a res =
  | Ok of 'a * st
  | Err of unify_error * st

type 'a unify = (st -> 'a res)

(* TODO: All of these should take positions as the first arguments *)

(** Do two types overlap on the argument types? Used to check for overlapping
  * definitions of overloaded identifiers. *)
let rec overlaps (free:TVSet.t) (tp1:typ) (tp2:typ) : unit unify =
  let rho1 = instantiate tp1 in
  let rho2 = instantiate tp2 in
  match (split_fun_type rho1, split_fun_type rho2) with
  (* values always overlap *)
  | (None,_) -> ()
  | (_,None) -> ()
  (* rest *)
  | (Some(targs1,_,_),Some(targs2,_,_)) ->
      let (fixed1,optional1) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs1) in
      let (fixed2,optional2) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs2) in
      let hi = Pervasives.max (List.length fixed1) (List.length fixed2) in
      let fo1 = List.take hi (fixed1 @ (List.map ~f:unoptional optional1)) in
      let fo2 = List.take hi (fixed2 @ (List.map ~f:unoptional optional1)) in
      if (List.length fo1 <> List.length fo2) then
        NoMatch     (* one has more fixed arguments than the other can ever get *)
      else ()

(** Does a type have the given named arguments *)
and match_named (tp:typ) (n:int) (named : name list) : unit unify =
  let rho1 = instantiate tp in
  match split_fun_type rho1 with
  | None -> unify_error NoMatch
  | Some(pars,_,_) ->
      if n + List.length named > List.length pars then
        unify_error NoMatch
      else
        let npars = List.drop pars n in
        let names = List.map ~f:fst npars in
        if List.for_all ~f:(List.mem names) named then
          let rest =
            let open List in do_;
            (* npars >>= fun (nm,tp) -> *)
            (* guard (not @@ List.mem named nm) >>= fun _ -> *)
            (* return tp *)
            (nm,tp) <-- npars;
            guard (not @@ mem named nm);
            return tp
          in
          if (List.for_all ~f:is_optional rest) then
            return ()
