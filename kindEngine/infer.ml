open Core
open Common
open Common.ConcreteSyntax
open Heart
open InferKind

(* Responsibilities of the kind checker:
 * - Kindcheck all types in the program
 * - Translate user types to internal types
 * - Collect lists of data types, synonyms and constructors
 * - Expand all synonyms (i.e., replace @id(int)@ by @id(int) == int@)
 * - Transate type definition groups and externals to Core. *)

(**************************************************************
 * Resolve kinds: from InfKind to Kind and UserType to Type
 **************************************************************)
let resolve_kind infkind = let open InferMonad in
  let rec resolve = function
    | InfKind.Var _      -> Kind.Prim.star
    | InfKind.Con k      -> k
    | InfKind.App(k1,k2) -> Kind.App(resolve k1, resolve k2)
  in 
  let%bind skind = subst infkind in
  return @@ resolve skind

let resolve_type_binder_def TypeBinder.{name; kind=infkind} = let open InferMonad in
  let%bind kind  = resolve_kind infkind in
  let%bind qname = qualify_def name in
  return TypeBinder.{name=qname; kind}

let resolve_type_binder TypeBinder.{name; kind=infkind} = let open InferMonad in
  let%bind kind = resolve_kind infkind in
  return TypeBinder.{name; kind}

(**
 * `resolve_type` takes: a map from locally quantified type name variables to types,
 * a boolean that is `true` if partially applied type synonyms are allowed (i.e. when
 * these are arguments to type synonyms themselves), a user type with inference kinds,
 * and it returns a fully resolved type. *)
let rec resolve_type idmap partial_syn user_type = let open InferMonad in
  let open KindedUserType in
  let open UserQuantifier in
  let rec collect_args tp args = match tp with
      | App(tp', args') -> collect_args tp' (args' @ args)
      | Parens(tp')     -> collect_args tp' args
      | Ann(tp',_)      -> collect_args tp' args
      | _               -> (tp, args)
  in
  let resolve_param (name,tp) =
    let%bind tp' = resolve_type idmap false tp in
    return (name,tp')
  in
  match user_type with
  | Quan(Forall, tname, tp) ->
      let%bind tname' = resolve_type_binder tname in
      let%bind tvar   = fresh_type_var tname' Kind.Flavour.Bound in
      let%bind tp'    = resolve_type (Name.Map.set idmap ~key:tname.TypeBinder.name ~data:tvar) false tp in
      return @@ Type.quantify [tvar] tp'

  | Quan(Some, tname, tp) -> 
      let%bind tname' = resolve_type_binder tname in
      let%bind tvar   = fresh_type_var tname' Kind.Flavour.Meta in
      let%bind tp'    = resolve_type (Name.Map.set idmap ~key:tname.TypeBinder.name ~data:tvar) false tp in
      return @@ Type.quantify [tvar] tp'

  | Quan(Exists, tname, tp) ->
      failwith "TODO: KindEngine.Infer.resolve_type: existentials are not supported yet"

  | Qual(preds,tp) ->
      let%bind preds' = mapM (resolve_predicate idmap) preds in
      let%bind tp'    = resolve_type idmap false tp in
      return @@ Type.qualify preds' tp'

  | Fun(args, effect, tp) ->
      let%bind args'   = mapM resolve_param args in
      let%bind effect' = resolve_type idmap false effect in
      let%bind tp'     = resolve_type idmap false tp in
      return @@ Type.TFun(args', effect', tp')

  | App(tp,args) -> resolve_app idmap partial_syn (collect_args tp args)
  | Var(name)    -> resolve_app idmap partial_syn (user_type, [])
  | Con(name)    -> resolve_app idmap partial_syn (user_type, [])
  | Parens(tp)   -> resolve_type idmap partial_syn tp
  | Ann(tp,_)    -> resolve_type idmap partial_syn tp

and resolve_predicate idmap tp = let open InferMonad in
  match%bind resolve_type idmap false tp with
  | Type.TCon(tc)                   -> return @@ Type.PredIFace(tc.name, [])
  | Type.TApp(Type.TCon(tc), targs) -> return @@ Type.PredIFace(tc.name, targs)
  | tp' -> failwithf "KindEngine.Infer.resolve_predicate: invalid predicate: %s" (Type.Show_typ.show tp') ()

and resolve_app idmap partial_syn = let open InferMonad in
  function
  | KindedUserType.Var(name), args ->
      let%bind (tp', kind) = match Name.Map.find idmap name with
        | None -> failwithf "Type variable %s is undefined" (Name.show name) ()
        (* let%bind id = Unique.id (Name.show name) in return (Type.TVar Type.{type_var_id=id; type_var_kind=Kind.Prim.star; type_var_flavour=Flavour.Bound}, Kind.Prim.star) *)
        | Some tvar -> return (Type.TVar(tvar), tvar.Type.TypeVar.kind)
      in
      let%bind args' = mapM (resolve_type idmap false) args in
      return @@ Type.type_app tp' args'

  | KindedUserType.Con(name), [fixed;ext] when Name.equal name Name.effect_append ->
      let%bind fixed' = resolve_type idmap false fixed in
      let%bind ext'   = resolve_type idmap false ext   in
      let (ls,tl) = Type.extract_ordered_effect fixed' in
      if not (Type.is_effect_empty tl) then
        failwith "Effects can only have one extension point";
      return @@ Type.shallow_effect_extend fixed' ext'

  | KindedUserType.Con(name), args ->
      let%bind qname, ikind = find_inf_kind name in
      let%bind kind         = resolve_kind ikind in begin
      match%bind lookup_syn_info name with 
      | Some(Type.{syn_info_name; syn_info_kind; syn_info_params; syn_info_typ; syn_info_rank; syn_info_doc} as syn) -> 
          (* check over/under application *)
          if not partial_syn && List.length args < List.length syn_info_params then
            failwithf "Type alias %s has too few arguments" (Name.show name) ();
          if List.length args > List.length syn_info_params then
            failwithf "Type alias %s has too many arguments" (Name.show name) ();
          let%bind args' = mapM (resolve_type idmap true) args in
          let tsyn = Type.TSyn({type_syn_name=syn_info_name;
                                type_syn_kind=syn_info_kind;
                                type_syn_rank=syn_info_rank;
                                type_syn_info=Some(syn)},
                               args',
                               TypeVar.HasTypeVar_typ.(TypeVar.sub_new (List.zip_exn syn_info_params args') |-> syn_info_typ))
          in return tsyn
            (* NOTE: on partially applied type synonyms, we get a funky body type with free parameters but this
             * s only inside synonyms arguments so we are ok. *)
      | None ->
          let%bind args' = mapM (resolve_type idmap false) args in
          return (Type.type_app (Type.TCon{name; kind}) args')
    end
      
  | _ -> failwith "KindEngine.Infer.resolve_app: this case should never occur after kind checking"

let resolve_typedef is_rec rec_names = let open InferMonad in
  let rec kind_arity = function
    | Kind.App(Kind.App(kcon, k1), k2) when Kind.equal kcon Kind.Prim.arrow -> k1::(kind_arity k2)
    | _ -> []
  in
  function 
  | TypeDef.Synonym{binder=syn; params; synonym=tp; vis; doc} ->
      let%bind syn' = resolve_type_binder_def syn in
      let%bind params' = mapM resolve_type_binder params in
      let%bind type_vars = mapM (fun param -> fresh_type_var param Kind.Flavour.Bound) params' in
      let tvar_map = Name.Map.of_alist_exn @@
        List.zip_exn (List.map ~f:(fun p -> p.TypeBinder.name) params') type_vars
      in
      let%bind tp' = resolve_type tvar_map true tp in
      (* eta-expand type synonyms *)
      let kind = syn'.kind in
      let arity = kind_arity kind in
      let eta_kinds = List.drop arity (List.length type_vars) in
      let eta_tp, eta_params =
        if List.is_empty eta_kinds then
          (tp', type_vars)
        else
          let eta_vars = List.map eta_kinds ~f:(fun kind -> Type.TypeVar.{id=Unique.unique_id "eta"; kind; flavour=Type.Flavour.Bound}) in
          (Type.type_app tp' (List.map ~f:(fun t -> Type.TVar t) eta_vars), type_vars @ eta_vars)
      in
      let syn_info = Type.{
          syn_info_name   = syn'.TypeBinder.name;
          syn_info_kind   = syn'.TypeBinder.kind;
          syn_info_params = eta_params;
          syn_info_typ    = eta_tp;
          syn_info_rank   = Type.max_synonym_rank eta_tp;
          syn_info_doc    = doc
        }
      in
      return @@ Expr.TypeDef.Synonym{syn_info; vis}

  | TypeDef.DataType{binder=newtp; params; constrs=constructors; sort; def=ddef; vis; is_extend; doc} ->
      let%bind newtp' =
        if is_extend then
          let%bind name, ikind = find_inf_kind newtp.name in
          let%bind kind = resolve_kind ikind in
          return TypeBinder.{name; kind}
        else
          resolve_type_binder_def newtp
      in
      let%bind params' = mapM resolve_type_binder params in
      let type_result = Type.TCon{name=newtp'.name; kind=newtp'.kind} in
      let%bind type_vars =
        let kargs, kres = Kind.extract_kind_fun newtp'.kind in
        if List.is_empty params' && not (List.is_empty kargs) then
          (* invent parameters if they are not given (and it has an arrow kind) *)
          forM kargs (fun karg -> return Type.TypeVar.{id=Unique.unique_id "k"; kind=karg; flavour=Kind.Flavour.Bound})
        else
          forM params' (fun param -> fresh_type_var param Kind.Flavour.Bound)
      in
      let tvar_map = Name.Map.of_alist_exn @@ List.zip_exn (List.map params' ~f:(fun p -> p.name)) type_vars in
      (* let%bind consinfos = 
       *   forM constructors (resolve_constructor newtp'.name sort (not )) *)
      assert false
        
let inf_typedef x = assert false

(**************************************************************
 * Setup type environment for recursive definitions
 **************************************************************)
let rec user_kind_to_inf_kind = let open InferMonad in
  function
  | UserKind.Con(name)    -> return @@ InfKind.Con(Kind.Constant name)
  | UserKind.Arrow(k1,k2) ->
      let%bind k1' = user_kind_to_inf_kind k1 in
      let%bind k2' = user_kind_to_inf_kind k2 in begin
        match (k1', k2') with
        | InfKind.Con(kk1), InfKind.Con(kk2) ->
            return @@ InfKind.Con(Kind.Prim.fun_1 kk1 kk2)
        | _ -> return @@ InfKind.App(k1',k2')
      end
  | UserKind.Parens(k) -> user_kind_to_inf_kind k
  | UserKind.None      -> fresh_kind

let bind_type_binder TypeBinder.{name; kind=user_kind} = let open InferMonad in 
  let%bind kind = user_kind_to_inf_kind user_kind in
  return @@ TypeBinder.{name; kind}

let bind_typedef tdef = let open InferMonad in (* extension *)
  let%bind TypeBinder.{name;kind} = bind_type_binder (TypeDef.binder tdef) in
  let is_extend = TypeDef.is_extend tdef in
  let%bind qname = if is_extend then return name else qualify_def name in
  return (TypeBinder.{name=qname;kind}, not is_extend)

(**************************************************************
 * Infer kinds for the type definition groups
 **************************************************************)
let check_recursion tdefs =
  if (List.length tdefs > 1) && (List.for_all tdefs ~f:TypeDef.is_synonym) then
    failwith "Type synonyms cannot be recursive";
  InferMonad.return ()

let inf_type_defs is_rec tdefs : Heart.Expr.TypeDef.group InferMonad.t = let open InferMonad in
  let%bind xinfgamma = mapM bind_typedef tdefs in
  let infgamma = List.map ~f:fst @@ List.filter ~f:snd xinfgamma in
  let%bind ctdefs = extend_inf_gamma infgamma @@ begin (* extend inference gamma, also checks for duplicates *)
    let names = List.map ~f:(fun TypeBinder.{name} -> name) infgamma in
    let%bind tdefs1 = mapM inf_typedef (List.zip_exn (List.map ~f:fst xinfgamma) tdefs) in
    mapM (resolve_typedef is_rec names) tdefs1
  end in
  check_recursion tdefs >> (* check for recursive type synonym definitions rather late so we spot duplicate definitions first *)
  return @@ ctdefs

let inf_type_def_group = let open TypeDefGroup in function
    | Rec tdefs   -> inf_type_defs true  tdefs
    | NonRec tdef -> inf_type_defs false [tdef]

let rec inf_type_def_groups = let open InferMonad in function
  | tdgroup::tdgroups ->
      let%bind ctdgroup = inf_type_def_group tdgroup in
      let%bind (ctdgroups,kgamma,syns) = extend_kgamma ctdgroup (inf_type_def_groups tdgroups) in
      return (ctdgroup::ctdgroups, kgamma, syns)
  | [] ->
      let%bind kgamma = get_kgamma in
      let%bind syns = get_synonyms in
      return ([],kgamma,syns)


(**************************************************************
 * Main function
 **************************************************************)
let infer_kinds
      (max_struct_fields : int)       (* max struct fields option *)
      (imports : ImportMap.t)         (* import aliases *)
      (kgamma0 : Assumption.kgamma)   (* initial kind gamma *)
      (syns0 : Synonyms.t)            (* initial list of synonyms *)
      program                         (* original program *)
  =
  let (cgroups, kgamma1, syns1) = InferMonad.run_kind_infer program.Program.name imports kgamma0 syns0 (inf_type_def_groups program.Program.typedefs) in
  assert false
