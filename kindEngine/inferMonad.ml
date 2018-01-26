open Core
open Common
open InferKind

type kst = KSub.t
type kenv = {
  (* cscheme : color_scheme; *)
  current_module : Name.t;
  imports : ImportMap.t;
  kgamma : Assumption.kgamma;
  infgamma : InfKGamma.t;
  synonyms : Synonyms.t
}

type 'a kresult = {
  result: 'a;
  (* errors: (range * doc) list; *)
  (* warnings: (range * doc) list; *)
  st: kst;
}

(* kinfer *)
module Let_syntax = struct
  type 'a t = kenv -> kst -> 'a kresult
  let map (ki:'a t) ~(f:'a -> 'b) : 'b t = fun env st ->
    let r = ki env st in
    {r with result = f (r.result) }
  let return (x:'a) : 'a t = fun env st -> {result=x; st}
  let bind (ki:'a t) ~(f:'a -> 'b t) : 'b t = fun env st ->
    let {result=x; (* errs1; warns1; *) st=st1} = ki env st in
    let {result=y; (* errs2; warns2; *) st=st2} = (f x) env st1 in
    {result=y; (* errors=errs1^errs2; warnings=warns1^warns2; *) st=st2}
end
include Monadic.Make(Let_syntax)

let run_kind_infer module_name imports kgamma synonyms (ki:'a t) =
  let imports' = Option.value ~default:imports @@
    ImportMap.extend (Name.to_short_module_name module_name) module_name imports
  in
  (ki {current_module=module_name; imports=imports'; kgamma; infgamma=Name.Map.empty; synonyms}
     KSub.empty).result


let get_kind_env : kenv t = fun env st -> {result=env; st}

(* let add_error range doc : unit t =
 *   add_range_info range Error(doc) >>
 *   fun env st -> {result=(); errors=[(range,doc)]; warnings=[]; st}
 * 
 * let add_warning range doc : unit t =
 *   add_range_info range Warning(doc) >>
 *   fun env st -> {result=(); errors=[]; warnings=[(range,doc)]; st} *)

let get_ksub : KSub.t t = fun env st -> {result=st; st}

let extend_ksub (sub:KSub.t) : unit t =
  fun env st -> {result=(); st=KSub.(sub @@@ st)}

(**********************************************************************
 * Operations
 **********************************************************************)

let fresh_kind =
  return @@ InfKind.Var(Unique.unique_id "k")

let fresh_type_var tb flavour =
  let open ConcreteSyntax.TypeBinder in
  let id = Unique.unique_id (Name.show tb.name) in
  return Heart.Type.({type_var_id=id; type_var_kind=tb.kind; type_var_flavour=flavour})

(* let subst x =
 *   let%bind sub = get_ksub in
 *   return (sub |=> x) *)

let get_kgamma =
  let%bind env = get_kind_env in
  return env.kgamma

let get_synonyms =
  let%bind env = get_kind_env in
  return env.synonyms

(** Extend the inference kind assumption; checks for shadowed definitions  *)
let extend_inf_gamma tbinders (ki:'a t) : 'a t =
  let open Common.ConcreteSyntax.TypeBinder in
  let check (infgamma:InfKGamma.t) tb =
    if Name.Map.mem infgamma tb.name then
      (* add_error name_range @@ Printf.sprintf "Type %s is already defined" (Name.show tb.name) *)
      failwith (Printf.sprintf "Type %s is already defined" (Name.show tb.name))
      (* return @@ Name.Map.set infgamma ~key:tb.name ~data:tb.kind (* replaces *) *)        
    else
      return @@ Name.Map.set infgamma ~key:tb.name ~data:tb.kind
  in
  let extend_unsafe tbinders ki =
    let inf_gamma = Name.Map.of_alist_exn @@ List.map tbinders ~f:(fun {name; kind} -> (name,kind)) in
    (* assumes left-biased union *)
    fun env st -> ki {env with infgamma=Name.Map.union inf_gamma env.infgamma} st
  in 
  let%bind env = get_kind_env in
  foldM check env.infgamma tbinders >>
  extend_unsafe tbinders ki

(** Extend the kind assumption; checks for shadowed definitions  *)
let extend_kgamma (tdefs:Heart.Expr.TypeDef.group) (ki:'a t) : 'a t =
  (* NOTE: duplication check already happens in extendInfGamma but
   * there can still be a clash with a definition in another inference group *)
  let name_kind = let open Heart.Expr.TypeDef in function
      | Synonym{syn_info} -> Heart.Type.(syn_info.syn_info_name, syn_info.syn_info_kind)
      | Data{data_info} -> Heart.Type.(data_info.data_info_name, data_info.data_info_kind)
  in
  let check (kgamma, tdefs) tdef =
    if Heart.Expr.TypeDef.is_extension tdef then
      return (kgamma, tdefs)
    else
      let (name,kind) = name_kind tdef in
      match Assumption.lookup_q name kgamma with
      | None -> return (Assumption.extend ~name ~data:kind kgamma, tdef::tdefs)
      | Some _ ->
          failwith (Printf.sprintf "Type %s is already defined" (Name.show name))
          (* return (kgamma, tdefs) *)
  in
  let extend_unsafe tdefs (ki:'a t) : 'a t =
    let new_kgamma = Assumption.new_dedup (List.map ~f:name_kind tdefs) in
    let ksyns = Synonyms.create (List.concat_map tdefs ~f:(function Heart.Expr.TypeDef.Synonym{syn_info} -> [syn_info] | _ -> [])) in
    fun env st -> ki {env with kgamma = Assumption.union env.kgamma new_kgamma;
                               synonyms = Synonyms.compose env.synonyms ksyns} st
  in
  let%bind env = get_kind_env in
  let%bind (_, tdefs') = foldM check (env.kgamma, []) tdefs in
  extend_unsafe List.(rev tdefs') ki

let inf_qualified_name (name:Name.t) : Name.t t =
  if not (Name.is_qualified name) then
    return name
  else
    let%bind env = get_kind_env in
    match ImportMap.expand name env.imports with
    | Second (name', alias) when Name.case_equal (Name.qualifier name) alias ->
        return name'
    | Second (_, alias) ->
        failwithf "module %s should be cased as %s" (Name.show name) (Name.show alias) ()
    | First [] ->
        failwithf "module %s is undefined" (Name.show name) ()
    | First aliases ->
        failwithf "module %s is ambiguous. It can refer to: %s" (Name.show name) (List.to_string aliases ~f:Name.show) ()

let find_inf_kind name0 range =
  let%bind env = get_kind_env in
  let (name,mb_alias) = match ImportMap.expand name0 env.imports with
    | Second (name', alias) -> (name', Some alias)
    | _                     -> (name0, None)
  in
  (* lookup locally
   * NOTE: also lookup qualified since it might be recursive definition 
   * TODO: check for the locally inferred names for casing too. *)
  match Name.Map.find env.infgamma name with
  | Some infkind -> return (name, infkind)
  | None -> match Assumption.lookup env.current_module name env.kgamma with
    | Found(qname,kind) ->
        let name' = if Name.is_qualified name then qname else (Name.unqualify qname) in
        if not (Name.case_equal name' name) then
          failwithf "type %s should be cased as %s." (Name.show @@ Name.unqualify name0) (Name.show @@ Name.unqualify name') ();
        if (Option.is_some mb_alias) && not (String.equal name0.Name.name_module (Name.show @@ Option.value_exn mb_alias)) then
          failwithf "module %s should be cased as %s." name0.Name.name_module (Name.show @@ Option.value_exn mb_alias) ();
        return (qname, InfKind.Con(kind))
    | NotFound ->
        failwithf "Type %s is not defined.\n  hint: bind the variable using 'forall<%s>'?" (Name.show name) (Name.show name) ()
    | Ambiguous names ->
        failwithf "Type %s is ambiguous. It can refer to: %s" (Name.show name) (List.to_string names ~f:Name.show) ()

let qualify_def name =
  let%bind env = get_kind_env in
  return (Name.qualify env.current_module name)

let find_kind name =
  let%bind env = get_kind_env in
  match Assumption.lookup env.current_module name env.kgamma with
  | Found(qname,kind) -> return (qname, kind)
  | _ -> failwithf "KindEngine.InferMonad.find_kind: unknown type constructor: %s" (Name.show name) ()

let lookup_syn_info name =
  let%bind env = get_kind_env in
  return (Synonyms.lookup name env.synonyms)
