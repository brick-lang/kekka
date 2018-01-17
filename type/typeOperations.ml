open Core
open Common
open Common.Util
open Type
open TypeVar

(*****************************************************
 * Fresh type variables
 *****************************************************)
let freshTVar (kind:Kind.kind) (flavour:Kind.flavour) : typ =
  TVar (fresh_type_var kind flavour)

(*****************************************************
   Instantiation
 *****************************************************)
type evidence = {
  ev_name : Heart.tname;
  ev_pred : pred
  (* ; ev_range : range *)
}

(* implicit *)
module HasTypeVar_evidence : HasTypeVarEx with type t = evidence = struct
  type t = evidence
  let substitute sub ({ev_pred = ep; _} as ev) =
    { ev with ev_pred = HasTypeVar_pred.substitute sub ep }
  let ftv {ev_pred = ep; _} = HasTypeVar_pred.ftv ep
  let btv {ev_pred = ep; _} = HasTypeVar_pred.btv ep
  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end

module HasTypeVar_evidence_list = HasTypeVar_list(HasTypeVar_evidence)

(* implicit *)
module Show_evidence : BasicClasses.Show with type t = evidence = struct
  type t = evidence
  let show {ev_pred = ep; _} = Show_pred.show ep
end

(** Instantiate a type *)
let rec instantiate (tp:typ) : rho =
  let (_,_,rho,_) = instantiate_ex tp in rho

and instantiate_ex (tp:typ) =
  let (ids, preds, rho, coref) = instantiate_ex_fl Kind.Meta tp in
  let (erho, coreg) = extend rho in
  (ids, preds, erho, coreg <.> coref)

and instantiate_no_ex (tp:typ) =
  let (ids, preds, rho, coref) = instantiate_ex_fl Kind.Meta tp in
  (ids, preds, rho, coref)

(** Ensure the result of function always gets an extensible effect type
  * This is necessary to do on instantiation since we simplify such effect variables
  * away during generalization. Effectively, the set of accepted programs does not 
  * change but the types look simpler to the user.  *)
and extend (tp:rho) : rho * (Heart.expr -> Heart.expr) =
  match expand_syn tp with
  | TFun (args, eff, res) ->
      let (ls, tl) = extract_ordered_effect eff in
      if is_effect_empty tl then
        let tv = freshTVar Kind.kind_effect Meta in
        let open_eff = effect_extends ls tv in
        let open_tp = TFun(args, open_eff, res) in
        (open_tp, fun core -> Heart.open_effect_expr eff open_eff tp open_tp core)
      else (tp, Util.id)
  | _ -> (tp, Util.id)

(** General instantiation for skolemize and instantiate  *)
and instantiate_ex_fl (flavour:Kind.flavour) (tp:typ)
  : (type_var list * evidence list * rho * (Heart.expr -> Heart.expr)) =
  match split_pred_type tp with
  | ([],[],rho) -> ([], [], rho, Util.id)
  | (vars, preds, rho) ->
      let (tvars, sub) = fresh_sub flavour vars in
      let srho : rho         = HasTypeVar_typ.(sub |-> rho) in
      let spreds : pred list = HasTypeVar_list_pred.(sub |-> preds) in
      let pnames = List.map ~f:pred_name spreds in
      let corevars = List.map pnames ~f:(fun name -> Heart.Var {var_name = name; var_info = Heart.InfoNone}) in
      let evidence = List.zip_exn pnames spreds
                     |> List.map ~f:(fun (name,pred) -> {ev_name = name; ev_pred = pred}) in
      (tvars, evidence, srho,
       (match corevars with [] -> Util.id | _ -> Util.id (* Heart.add_apps corevars*)) <.> Heart.add_type_apps tvars)

and pred_name (pred:pred) : Heart.tname =
  let name = match pred with PredSub _ -> Heart.fresh_name "sub"
                           | PredIFace (iname,_) -> Heart.fresh_name (Name.show_name iname)
  in (name, Type.pred_type pred)

and fresh_sub_x (makeTVar:type_var -> typ) (flavour:Kind.flavour) (vars:type_var list) : type_var list * sub =
  let tvars = List.map ~f:(fun tv -> fresh_type_var tv.type_var_kind flavour) vars in
  let sub = sub_new (List.zip_exn vars (List.map tvars ~f:makeTVar)) in
  (tvars, sub)

and fresh_sub f v = fresh_sub_x (fun x -> TVar x) f v

(* Skolemize a type and return the instantiated quantifiers, name/predicate pairs for evidence, 
 * the instantiated type, and a core transformer function (which applies type arguments and evidence) *)
let skolemize_ex = instantiate_ex_fl Skolem

(* Skolemize a type *)
let skolemize (tp:typ) : rho = let (_,_,rho,_) = skolemize_ex tp in rho
