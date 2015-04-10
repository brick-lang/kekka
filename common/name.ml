
open Core.Std

(********************************* 
 * Names
 *********************************)
(**
 * Names defined by the user.
 * Uses a hash to speed up comparisons. The hash is constructed
 * such that they can be compared too. (h1 > h2 => name1 > name2)
 * The hash is case-insensitive, just like comparisons on names.
 * Use 'name_case_equal' for case-sensitive comparisons. 
 *)
type name = 
  {
    name_module : string;
    hash_module : int;
    name_id     : string;
    hash_id     : int;
  }

type names = name list

let name_case_equal
    { name_module = m1; name_id = n1; _ }
    { name_module = m2; name_id = n2; _ } =
  
  (m1 = m2) && (n1 = n2)
  
(* Checks whether both names are in the same namespace *)
let is_same_namespace name1 name2 =
  if (String.length name1.name_id > 0) && (String.length name2.name_id > 0) then
    (Char.is_uppercase name1.name_id.[0]) = (Char.is_uppercase name2.name_id.[0])
  else true

let name_case_overlap name1 name2 =
  (not @@ name_case_equal name1 name2) && (is_same_namespace name1 name2)

let lower_compare
    { name_module = m1; name_id = n1; _ }
    { name_module = m2; name_id = n2; _ } =
  match compare (String.lowercase m1) (String.lowercase m2) with
  | 0 -> compare (String.lowercase n1) (String.lowercase n2)
  | lg -> lg

let equal
    ({ hash_module = hm1; hash_id = hn1; _ } as n1)
    ({ hash_module = hm2; hash_id = hn2; _ } as n2) =
  
  (hn1 = hn2) && (hm1 = hm2) && (lower_compare n1 n2 = 0)

let compare 
    ({ hash_module = hm1; hash_id = hn1; _ } as n1)
    ({ hash_module = hm2; hash_id = hn2; _ } as n2) =
  match compare hm1 hm2 with
  | 0 -> (match compare hn1 hn2 with
      | 0 -> lower_compare n1 n2
      | lg -> lg)
  | lg -> lg 

let show { name_module = m; name_id = n; _ } =
  if String.is_empty m
  then n    
  else m ^ "/" ^ 
       let c = String.get m 0 in (* We're guranteed non-zero length *)
       if not (Char.is_alpha c || c = '_' || c ='(') then
         "(" ^ n ^ ")"
       else n

(** Show quotes around the name *)
let show_name name = "\"" ^ (show name) ^ "\""

let new_qualified m n = 
  let short s = String.of_char_list @@ List.take (String.to_list @@ String.lowercase s) 4 in
  let hash s = String.fold ~init:0 ~f:(fun h c -> h*256 + (Char.to_int c)) (short s) in
  { name_module = m; hash_module = (hash m); name_id = n; hash_id = (hash n)}

let create s = new_qualified "" s

let nil = create ""

let is_nil { name_module = m; name_id = n; _ } = String.is_empty n

let qualify ({ name_module = x; name_id = m; hash_id = hm; _ } as n1)
    ({ name_module = y; name_id = n; hash_id = hn; _ } as n2) =
    if ((String.is_empty x) && (String.is_empty y)) ||
       ((String.is_empty x) && (m = y)) then
      { name_module = m; hash_module = hm; name_id = n; hash_id = hn }
    else
      failwithf "Common.Name.qualify: Cannot use qualify on qualified names: (%s, %s)"
        (show n1) (show n2) ()

let unqualify { name_id = n; hash_id = hn; _ } =
  { name_module = ""; hash_module = 0; name_id = n; hash_id = hn }

let is_qualified { name_module = m; _ } =
  not @@ String.is_empty m

let qualifier { name_module = m; hash_module = hm; _} =
  { name_module = ""; hash_module = 0; name_id = m; hash_id = hm }

(**************************************************
 * Modules paths
 **************************************************)

let rec split_module_name name =
  if (is_qualified name) then
    split_module_name (qualifier name)
  else List.map ~f:create @@ String.split ~on:'/' (show name)

let unsplit_module_name xs =
  create @@ String.concat ?sep:(Some "/") (List.map ~f:show xs)


(**************************************************
 * wildcards & constructors
 **************************************************)

let is_wildcard name =
  (String.length name.name_id) > 0 &&
  (String.get name.name_id 0) = '_'

let is_constructor_name name =
  if (String.length name.name_id) > 0 then
    let c = (String.get name.name_id 0) in
    (Char.is_uppercase c) || (c = '(')
  else false


let to_constructor_name name =
  new_qualified name.name_module @@ String.capitalize name.name_id


(**************************************************
 * wildcards & constructors
 **************************************************)

let new_hidden_name s =
  create ("." ^ s)

let is_hidden_name name =
  (String.length name.name_id) > 0 &&
  (String.get name.name_id 0) = '.'

let new_field_name i =
  new_hidden_name ("field" ^ (show i))

let is_field_name = is_hidden_name

let new_implicit_type_var_name i =
  new_hidden_name ("t" ^ (show i))
    
let is_implicit_type_var_name = is_hidden_name

let new_hidden_external_name name =
  new_hidden_name ((show name) ^ "@extern")

(** Create a constructor creator name from the constructor name.
  * Used if special creation functions are used for the constructor.
  * in particular for the case of optional arguments. *)
let prepend s name =
  new_qualified name.name_module (s ^ name.name_id)

let postpend s name = 
  new_qualified name.name_module (name.name_id ^ s)

let new_creator_name = 
  prepend ".create"


(**************************************************
 * camel-case to dash-case
 **************************************************)

let split_camel s =
  let rec split_camel_list = function
    | [] -> []
    | c::cs when c = '-' -> split_camel_list cs
    | c::cs ->
      let is_break c = (Char.is_uppercase c || c = '-') in
      let all_but_last l = List.take l @@ (List.length l) - 1 in
      let (pre, post) = List.split_while ~f:(fun c -> not @@ is_break c) cs in
      if List.is_empty pre then
        let (pre2,post2) = List.split_while ~f:Char.is_uppercase post in
        if List.is_empty pre2 || (not (List.is_empty post2) && is_break (List.hd_exn post2))
        then (c::pre2) :: split_camel_list post2
        else (c::(all_but_last pre2)) :: split_camel_list ((List.last_exn pre2)::post2)
      else (c::pre) :: split_camel_list post
  in
  let char_list_to_string = List.fold_right ~init: "" ~f: (fun c cs -> (Char.to_string c) ^ cs) in 
  String.to_list s |> split_camel_list |> List.map ~f:char_list_to_string


let camel_to_dash s =
  match List.map ~f:String.lowercase (split_camel s) with
  | x::xs -> List.fold_left ~init:x ~f: (fun y ys -> y ^ "-" ^ ys) xs
  | [] -> ""

(**************************************************
 * camel-case to dash-case
 **************************************************)
