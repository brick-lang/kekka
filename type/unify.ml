open Core.Std
open Util
open Type

(* Unify monad *)

type st = { uniq : int; sub : TypeVar.sub }

(* type 'a unify = Unify of  *)

(* TODO: All of these should take positions as the first arguments *)

(** Do two types overlap on the argument types? Used to check for overlapping
 * definitions of overloaded identifiers. *)
let rec overlaps free tp1 tp2 =
  let rho1 = instantiate tp1
  and rho2 = instantiate tp2 in
  match (split_fun_type rho1, split_fun_type rho2) with
  (* values always overlap *)
  | (None,_) -> ()
  | (_,None) -> ()
  (* rest *)
  | (Some(targs1,_,_),Some(targs2,_,_)) ->
      (* if (List.length targs1 <> List.length targs2) then *)
      (*   unifyError NoMatch *)
      (* else unifies (List.map ~f:snd targs1) (List.map ~f:snd targs2) *)
      let (fixed1,optional1) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs1) in
      let (fixed2,optional2) = List.split_while ~f:(not <.> is_optional) (List.map ~f:snd targs2) in
      let len1 = List.length fixed1 in
      let len2 = List.length fixed2 in
      if ((List.is_empty optional1 && len1 < len2) || (List.is_empty optional2 && len1 > len2)) then
        unify_error NoMatch
      else
        let lo = min len1 len2 in
        unifies (List.take lo fixed1) (List.take lo fixed2);
        return ()     (* TODO: this is slightly too strict: if the longest prefix of fixed arguments match, we consider them overlapped  *)


and match_named tp n named =
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
