open Core
open Common
open Common.Util

(* Kind assumptions *)
type kgamma = Inner.kind QNameMap.t

let empty  = QNameMap.empty
let single = QNameMap.single
let create = QNameMap.of_list
let new_dedup xs = QNameMap.of_list @@ List.dedup ~compare:(fun (n1,x) (n2,y) -> Name.compare n1 n2) xs
                         
let extend = QNameMap.insert
let lookup = QNameMap.lookup
let lookup_q = QNameMap.lookup_q (* Lookup a fq-name *)
let find ctxt name kg = match lookup ctxt name kg with
  | QNameMap.Found(qname,scheme) -> (qname,scheme)
  | _ -> Failure.failure ("Kind.Assumption.kgammaFind: unbound type '" ^ Name.show_name name ^ "' in " ^
                          List.to_string ~f:(fun (k,v) -> "(" ^ Name.show_name k ^ ") => " ^ Inner.Show_kind.show v) @@ QNameMap.to_alist kg)

let to_list kg = List.sort ~cmp:(fun (n1,_) (n2,_) -> Name.compare n1 n2) @@ QNameMap.to_alist kg
let filter mod_name = QNameMap.filter_names ~f:(Name.equal mod_name <.> Name.qualifier)
  
(** kind gamma union; error on duplicates *)
let union = QNameMap.union
let union_list = QNameMap.union_list
                   

(****************************************************
 * Initial kind gamma 
 ****************************************************)
(** The initial kind gamma contains the 'builtinTypes'. *)
let init = empty
let is_empty = QNameMap.is_empty
