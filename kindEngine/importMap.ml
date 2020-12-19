open Core
open Common
open Common.Util
       
(** 
 * Maps short module aliases @core@ to full module paths @std/core@.
 * It is represented as a map from a reversed list of module path components to a full name
 * i.e. import my/core = std/core  ->  [(["core","my"], "std/core"); ...] *)    
type t = (Name.t list * Name.t) list

let empty = []

let extend name fq_name (imp_map:t) =
  let rpath = List.rev @@ Name.split_module_name name in
  (* make sure it's not already there *)
  if List.Assoc.mem imp_map rpath ~equal:(List.equal Name.equal) then
    None
  else
    Some((rpath,fq_name)::imp_map)

(**
 * `expand name map` takes a qualified name (`core/int`) and expands
 * it to its real fully qualified name (`std/core/int`). It also returns
 * the declared alias suffix (used to find case-errors). 
 * On ambiguity, or if not found at all, it returns First with a list of candidates. *)
let expand name (imp:t) : (Name.t list, (Name.t * Name.t)) Either.t =
  let rec is_prefix x y = match x,y with
    | x::xs, y::ys -> (Name.equal x y) && is_prefix xs ys
    | [], _        -> true
    | _            -> false
  in 
  if Name.is_qualified name then
    let rpath = List.rev @@ Name.split_module_name (Name.qualifier name) in
    match List.filter imp ~f:(fun (ralias,_) -> is_prefix rpath ralias) with
    | [(ralias,full_name)] -> 
        Either.Second (Name.qualify full_name (Name.unqualify name),
                       Name.unsplit_module_name List.(rev @@ take ralias (length rpath)))
    | amb -> Either.First (List.map amb ~f:Util.(fst >>> List.rev >>> Name.unsplit_module_name))
  else
    Either.Second (name, Name.nil)


(* Given a fully qualified name, return the shorter aliased name.
 * For example, with `import System.Foo as F` a name `System.Foo.bar` is shortened to `F.bar`. *)
let alias name imp : Name.t =
  let module_name = if Name.is_qualified name then Name.qualifier name else name in
  match List.filter imp ~f:(fun (_,fullname) -> Name.equal module_name fullname) with
  | [(ralias,_)] ->
      let alias = Name.unsplit_module_name (List.rev ralias) in
      if Name.is_qualified name then Name.qualify alias (Name.unqualify name) else alias
  | _ -> name  


let to_list : t -> (Name.t * Name.t) list =
  List.map ~f:(fun (ralias,fullname)-> (Name.unsplit_module_name (List.rev ralias), fullname))
