open Core
open Util
open Type
(* open TypeVar *)
open TypeOperations

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

(* TODO: this might need to be lazy *)
module UnifyM = struct
  type 'a t = (st -> 'a res)
  let return (x:'a) : 'a t = fun st -> Ok(x,st)
  let bind (u:'a t) (f: 'a -> 'b t) : 'b t = fun st1 ->
    match u st1 with
    | Ok(x,st2) -> (f x) st2
    | Err(err,st2) -> Err(err,st2)
  let unify_error err : 'a t = fun st -> Err(err,st)
end
open UnifyM
let (>>=) = bind

(* TODO: All of these should take positions as the first arguments *)

(** Do two types overlap on the argument types? Used to check for overlapping
  * definitions of overloaded identifiers. *)
let overlaps (free:TypeVar.TVSet.t) (tp1:typ) (tp2:typ) : unit UnifyM.t =
  let rho1 = instantiate tp1 in
  let rho2 = instantiate tp2 in
  match (split_fun_type rho1, split_fun_type rho2) with
  (* values always overlap *)
  | (None,_) -> return ()
  | (_,None) -> return ()
  (* rest *)
  | (Some(targs1,_,_),Some(targs2,_,_)) ->
      let (fixed1,optional1) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs1) in
      let (fixed2,optional2) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs2) in
      let hi = Pervasives.max (List.length fixed1) (List.length fixed2) in
      let fo1 = (Util.flip List.take) hi (fixed1 @ (List.map ~f:unoptional optional1)) in
      let fo2 = (Util.flip List.take) hi (fixed2 @ (List.map ~f:unoptional optional1)) in
      if ((List.length fo1) <> (List.length fo2)) then
        unify_error NoMatch     (* one has more fixed arguments than the other can ever get *)
      else return ()

(** Does a type have the given named arguments *)
let match_named (tp:typ) (n:int) (named : Name.name list) : unit UnifyM.t =
  let rho1 = instantiate tp in
  match split_fun_type rho1 with
  | None -> unify_error NoMatch
  | Some(pars,_,_) ->
      if (n + List.length named) > List.length pars then
        unify_error NoMatch
      else
        let npars = List.drop pars n in
        let names = List.map ~f:fst npars in
        if List.for_all ~f:(List.mem names ~equal:Name.eq_name) named then
          (* [tp | (nm,tp) <- npars, not (nm `elem` named)] *)
          let rest = List.(npars >>= fun (nm,tp) ->
                           guard (not @@ mem named nm ~equal:Name.eq_name) >>= fun _ ->
                           return tp)
          in 
          if (List.for_all ~f:is_optional rest) then
            return ()
          else unify_error NoMatch
        else unify_error NoMatch

