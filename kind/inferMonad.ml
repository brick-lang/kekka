open Core
open Common

type kst = InferKind.ksub
type kenv = {
  (* cscheme : color_scheme; *)
  current_module : Name.t;
  imports : ImportMap.t;
  kgamma : Assumption.kgamma;
  infgamma : InferKind.inf_kgamma;
  (* synonyms : Synonyms.t *)
}

type 'a kresult = {
  result: 'a;
  (* errors: (range * doc) list; *)
  (* warnings: (range * doc) list; *)
  st: kst;
}

type 'a t = kenv -> kst -> 'a kresult
