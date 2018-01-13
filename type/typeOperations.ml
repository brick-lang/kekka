open TypeVar

type tname = Type.typ * Name.name
type evidence = {
  ev_name : tname;
  ev_pred : pred
  (* ; ev_range : range *)
}

(* implicit *)
module HasTypeVar_evidence : HasTypeVar with type t = evidence = struct
  type t = evidence
  let substitute sub ({ev_pred = ep; _} as ev) =
    { ev with ev_pred = HasTypeVar_pred_rec.substitute sub ep }
  let ftv {ev_pred = ep; _} = HasTypeVar_pred_rec.ftv ep
  let btv {ev_pred = ep; _} = HasTypeVar_pred_rec.btv ep
end

(* implicit *)
module Show_evidence : Show with type t = evidence = struct
  type t = evidence
  let show {ev_pred = ep; _} = Show_pred.show ep
end

(** Instantiate a type *)
(* let instantiate {m:HasUnique} (range:range) (tp:typ) : m rho *)
let instantiate (tp:typ) =
  let (ids, preds, rho, coref) = instantiate_ex tp in
  rho

and instantiate_ex (tp:typ) =
  let (ids, preds, rho, coref) = instantiate_ex_f1 Type.Meta tp in
  let (erho, coreg) = extend rho in
  (ids, preds, erho, coreg <.> coref)

and instantiate_no_ex (tp:typ) =
  let (ids, preds, rho, coref) = instantiate_ex_f1 Type.Meta tp in
  (ids, preds, rho, coref)

(* and extend (tp:rho) = match Type.expand_syn tp with *)
(*   | Type.TFun(args,eff,res) -> *)
(*       let (ls, tl) = Type.extract_ordered_effect eff in *)
(*       if Type.is_effect_empty tl then *)
(*         let tv = fresh_tvar kind_effect Type.Meta in *)
(*         let open_eff =  *)
