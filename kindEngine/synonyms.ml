open Core
open Common
open Common.Util
open Heart
(* Instantiate type synonyms *)

(* Synonyms: a map from type synonym names to a tuple of a synonym
 * type scheme ('SynInfo'), an integer that gives the relative _rank_ of the type synonym *)
type t = Type.syn_info Name.Map.t

let empty : t = Name.Map.empty
let is_empty : t -> bool = Name.Map.is_empty
let create : Type.syn_info list -> t =
  Name.Map.of_alist_exn <.> List.map ~f:(fun syninfo -> syninfo.Type.syn_info_name, syninfo)

let type_defs : t -> t = id
let extend (syn_info:Type.syn_info) (m:t) : t = Name.Map.add m ~key:syn_info.Type.syn_info_name ~data:syn_info
let lookup (name:Name.t) (map:t) : Type.syn_info option = Name.Map.find map name
let compose (m1:t) (m2:t) : t = Name.Map.union m1 m2
let find (name:Name.t) (syn:t) =
  match lookup name syn with
  | None -> Failure.failure ("KindEngine.Synonyms.find: unknown type synonym:" ^ Name.show_name name)
  | Some x -> x

let filter (mod_name:Name.t) (s:t) =
  Name.Map.filter_keys s ~f:(fun name -> Name.equal (Name.qualifier name) mod_name)

let to_list (syns:t) : Type.syn_info list = List.map ~f:snd (Name.Map.to_alist syns)
(* let pretty (syns:t) = *)

(** Extract synonym environment from core program *)
(* let extract_synonyms core = Name.Map.union *)

let extract_type_def : Expr.TypeDef.t -> t = function
  | Expr.TypeDef.Synonym { syn_info; vis=Syntax.Public } ->
      Name.Map.singleton syn_info.Type.syn_info_name syn_info
  | _ -> Name.Map.empty

let extract_type_def_group (tdefs:Expr.TypeDef.group) =
  List.map ~f:extract_type_def tdefs
