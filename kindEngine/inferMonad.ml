open Core
open Common

type kst = InferKind.ksub
type kenv = {
  (* cscheme : color_scheme; *)
  current_module : Name.t;
  imports : ImportMap.t;
  kgamma : Assumption.kgamma;
  infgamma : InferKind.inf_kgamma;
  synonyms : Synonyms.t
}

type 'a kresult = {
  result: 'a;
  (* errors: (range * doc) list; *)
  (* warnings: (range * doc) list; *)
  st: kst;
}

(* kinfer *)
include Monadic.Make(struct
    type 'a t = kenv -> kst -> 'a kresult
    let map (ki:'a t) ~(f:'a -> 'b) : 'b t = fun env st ->
      let r = ki env st in
      {r with result = f (r.result) }
    let return (x:'a) : 'a t = fun env st -> {result=x; st}
    let bind (ki:'a t) ~(f:'a -> 'b t) : 'b t = fun env st ->
      let {result=x; (* errs1; warns1; *) st=st1} = ki env st in
      let {result=y; (* errs2; warns2; *) st=st2} = (f x) env st1 in
      {result=y; (* errors=errs1^errs2; warnings=warns1^warns2; *) st=st2}
  end)

let run_kind_infer module_name imports kgamma synonyms (ki:'a t) =
  let imports' = Option.value ~default:imports @@
    ImportMap.extend (Name.to_short_module_name module_name) module_name imports
  in
  let r = ki {current_module=module_name; imports=imports'; kgamma; infgamma=Name.Map.empty; synonyms}
            InferKind.ksub_empty
  in 
  r.result

let get_kind_env : kenv t = fun env st -> {result=env; st}

(* let add_error range doc : unit t =
 *   add_range_info range Error(doc) >>
 *   fun env st -> {result=(); errors=[(range,doc)]; warnings=[]; st}
 * 
 * let add_warning range doc : unit t =
 *   add_range_info range Warning(doc) >>
 *   fun env st -> {result=(); errors=[]; warnings=[(range,doc)]; st} *)

let get_ksub : InferKind.ksub t = fun env st -> {result=st; st}

let extend_ksub (sub:InferKind.ksub) : unit t =
  fun env st -> {result=(); st=InferKind.(sub @@@ st)}

(**********************************************************************
 * Operations
 **********************************************************************)

let fresh_kind =
  return @@ InferKind.KIVar(Unique.unique_id "k")

(* let fresh_type_var = *) 
