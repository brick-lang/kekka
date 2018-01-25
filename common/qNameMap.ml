open Core

module M = Map.Make(Name)
type 'a t = (Name.t *'a) list M.t
type 'a lookup =
  | Found     of Name.t * 'a
  | Ambiguous of Name.t list
  | NotFound

let empty    : 'a t         = M.empty
let is_empty : 'a t -> bool = M.is_empty
                                
let single name x :'a t = M.singleton (Name.unqualify name) [(name,x)]

(** Lookup a fully qualified name  *)
let lookup_q (name:Name.t) (m:'a t) : 'a option =
  match M.find m (Name.unqualify name) with
  | None -> None
  | Some xs -> List.Assoc.find xs name ~equal:Name.equal

(** Lookup a potentially unqualified name within a module context. 
  * (The module context is ignored if a qualified name is looked up) *)
let lookup (context:Name.t) (name:Name.t) (m:'a t) : 'a lookup =
  match M.find m (Name.unqualify name) with
  | None -> NotFound
  | Some [(qname,x)] when not (Name.is_qualified name) -> Found(qname,x)
  | Some xs ->
      let qname = if Name.is_qualified name then name else Name.qualify context name in
      match List.filter xs ~f:(fun p -> Name.equal (fst p) qname) with
      | [(realname,x)] -> Found(realname,x)
      | _ -> Ambiguous (List.map ~f:fst xs)

let filter_names ~(f:Name.t -> bool) : 'a t -> 'a t =
  M.map ~f:(List.filter ~f:(fun (name,_) -> f name))
                                                        
let safe_combine (caller:string) (xs:(Name.t * 'a) list) (ys:(Name.t * 'a) list) : (Name.t * 'a) list =
  let ynames = List.map ys fst in
  let xnames = List.map xs fst in
  if List.exists xnames ~f:(List.mem ynames ~equal:Name.equal) then
    failwithf "Common.QNameMap.%s: overlapping names: (%s, %s)"
      caller (List.to_string ~f:Name.show xnames) (List.to_string ~f:Name.show ynames) ()
  else xs @ ys

let insert ~(name:Name.t) ~(data:'a) (m:'a t) : 'a t =
  M.change m (Name.unqualify name)
    ~f:(function None    -> Some [(name,data)]
               | Some ys -> Some (safe_combine "insert" [(name,data)] ys))

let of_list : (Name.t * 'a) list -> 'a t =
  List.fold ~init:empty ~f:(fun qm (name,data) -> insert qm ~name ~data)

let union (m1:'a t) (m2:'a t) : 'a t = 
  List.fold (M.to_alist m2) ~init:m1 ~f:(fun acc (key,data) ->
      M.change acc key ~f:(function None    -> Some data
                                  | Some ys -> Some (safe_combine "union" data ys)))

let union_list (qs:'a t list) : 'a t = List.fold ~init:empty ~f:union qs

let to_alist (m:'a t) : (Name.t * 'a) list = List.concat_map ~f:snd (M.to_alist m)
