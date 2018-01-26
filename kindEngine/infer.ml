open Heart
open InferKind
     
(* Responsibilities of the kind checker:
 * - Kindcheck all types in the program
 * - Translate user types to internal types
 * - Collect lists of data types, synonyms and constructors
 * - Expand all synonyms (i.e., replace @id(int)@ by @id(int) == int@)
 * - Transate type definition groups and externals to Core. *)
(**************************************************************
 * Setup type environment for recursive definitions
 **************************************************************)

let rec user_kind_to_kind =
  let open InferMonad in
  let open Common.ConcreteSyntax in
  function
  | UserKind.Con(name)    -> return @@ InfKind.Con(Kind.KCon name)
  | UserKind.Arrow(k1,k2) ->
      let%bind k1' = user_kind_to_kind k1 in
      let%bind k2' = user_kind_to_kind k2 in begin
        match (k1', k2') with
        | InfKind.Con(kk1), InfKind.Con(kk2) ->
            return @@ InfKind.Con(Kind.kind_fun kk1 kk2)
        | _ -> return @@ InfKind.App(k1',k2')
      end
  | UserKind.Parens(k) -> user_kind_to_kind k
  | UserKind.None -> fresh_kind
    
(* let bind_type_def tdef = *)        (* extension *)
  

(**************************************************************
 * Infer kinds for the type definition groups
 **************************************************************)
                            
let inf_type_defs is_rec tdefs = assert false
  (* let%bind x *)

let inf_type_def_group = let open Common.ConcreteSyntax.TypeDefGroup in function
    | Rec tdefs -> inf_type_defs true tdefs
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

let infer_kinds
      (max_struct_fields : int)       (* max struct fields option *)
      (imports : ImportMap.t)         (* import aliases *)
      (kgamma0 : Assumption.kgamma)   (* initial kind gamma *)
      (syns0 : Synonyms.t)            (* initial list of synonyms *)
      program                         (* original program *)
  =
  let open Common.ConcreteSyntax in
  let (cgroups, kgamma1, syns1) = InferMonad.run_kind_infer program.Program.name imports kgamma0 syns0 (inf_type_def_groups program.Program.typedefs) in
  assert false
