open Core
open Common
open Common.Util
open Heart
open TypeVar

(*****************************************************
 * Fresh type variables
 *****************************************************)
let freshTVar (kind:Kind.t) (flavour:Type.Flavour.t) : Type.typ =
  TVar (fresh_type_var kind flavour)

(*****************************************************
   Instantiation
 *****************************************************)
module Evidence = struct
  type t = {
    name : Expr.tname;
    pred : Type.pred;
    (* range : Range.t; *)
  }

  let show {pred = ep; _} = Type.Show_pred.show ep

  (* HasTypeVar *)
  let substitute sub ({pred = ep; _} as ev) =
    { ev with pred = HasTypeVar_pred.substitute sub ep }
  let ftv {pred = ep; _} = HasTypeVar_pred.ftv ep
  let btv {pred = ep; _} = HasTypeVar_pred.btv ep
  let (|->) sub x = if sub_is_null sub then x else substitute sub x
end

module HasTypeVar_evidence_list = HasTypeVar_list(Evidence)

(** Instantiate a Type.type *)
let rec instantiate (tp:Type.typ) : Type.rho =
  let (_,_,rho,_) = instantiate_ex tp in rho

and instantiate_ex (tp:Type.typ) =
  let (ids, preds, rho, coref) = instantiate_ex_fl Type.Flavour.Meta tp in
  let (erho, coreg) = extend rho in
  (ids, preds, erho, coreg <.> coref)

and instantiate_no_ex (tp:Type.typ) =
  let (ids, preds, rho, coref) = instantiate_ex_fl Meta tp in
  (ids, preds, rho, coref)

(** Ensure the result of function always gets an extensible effect Type.type
  * This is necessary to do on instantiation since we simplify such effect variables
  * away during generalization. Effectively, the set of accepted programs does not 
  * change but the Type.types look simpler to the user.  *)
and extend (tp:Type.rho) : Type.rho * (Expr.expr -> Expr.expr) =
  match Type.expand_syn tp with
  | TFun (args, eff, res) ->
      let (ls, tl) = Type.extract_ordered_effect eff in
      if Type.is_effect_empty tl then
        let tv = freshTVar Kind.Prim.effect Meta in
        let open_eff = Type.effect_extends ls tv in
        let open_tp = Type.TFun(args, open_eff, res) in
        (open_tp, fun core -> Expr.open_effect_expr eff open_eff tp open_tp core)
      else (tp, Util.id)
  | _ -> (tp, Util.id)

(** General instantiation for skolemize and instantiate  *)
and instantiate_ex_fl (flavour:Type.Flavour.t) (tp:Type.typ)
  : (Type.type_var list * Evidence.t list * Type.rho * (Expr.expr -> Expr.expr)) =
  match Type.split_pred_type tp with
  | ([],[],rho) -> ([], [], rho, Util.id)
  | (vars, preds, rho) ->
      let (tvars, sub) = fresh_sub flavour vars in
      let srho : Type.rho = HasTypeVar_typ.(sub |-> rho) in
      let spreds : Type.pred list = HasTypeVar_list_pred.(sub |-> preds) in
      let pnames = List.map ~f:pred_name spreds in
      let corevars = List.map pnames ~f:(fun name -> Expr.Var {var_name = name; var_info = Expr.InfoNone}) in
      let evidence = List.zip_exn pnames spreds
                     |> List.map ~f:(fun (name,pred) -> Evidence.{name = name; pred = pred}) in
      (tvars, evidence, srho,
       (match corevars with [] -> Util.id | _ -> Util.id (* add_apps corevars*)) <.> Expr.add_type_apps tvars)

and pred_name (pred:Type.pred) : Expr.tname =
  let name = match pred with Type.PredSub _ -> Expr.fresh_name "sub"
                           | Type.PredIFace (iname,_) -> Expr.fresh_name (Name.show iname)
  in (name, Type.pred_type pred)

and fresh_sub_x (makeTVar:Type.type_var -> Type.typ) (flavour:Type.Flavour.t) (vars:Type.type_var list) : Type.type_var list * sub =
  let tvars = List.map ~f:(fun tv -> fresh_type_var tv.Type.type_var_kind flavour) vars in
  let sub = sub_new (List.zip_exn vars (List.map tvars ~f:makeTVar)) in
  (tvars, sub)

and fresh_sub f v = fresh_sub_x (fun x -> TVar x) f v

(* Skolemize a Type.type and return the instantiated quantifiers, name/predicate pairs for evidence, 
 * the instantiated Type.type, and a core transformer function (which applies Type.type arguments and evidence) *)
let skolemize_ex = instantiate_ex_fl Skolem

(* Skolemize a Type.type *)
let skolemize (tp:Type.typ) : Type.rho = let (_,_,rho,_) = skolemize_ex tp in rho
