open Core.Std

type names = name list

(**
 * Names defined by the user.
 * Uses a hash to speed up comparisons. The hash is constructed
 * such that they can be compared too. (h1 > h2 => name1 > name2)
 * The hash is case-insensitive, just like comparisons on names.
 * Use 'name_case_equal' for case-sensitive comparisons. 
 *)
and name = 
  {
    name_module : string;
    hash_module : int;
    name_id     : string;
    hash_id     : int;
  }

let rec name_case_equal {name_module = m1; name_id = n1; _}  {name_module = m2; name_id = n2; _} =
  m1 = m2 && n1 = n2
  
and name_case_overlap name1 name2 =
  (not @@ name_case_equal name1 name2) && (is_same_namespace name1 name2)

(* Checks whether both names are in the same namespace *)
and is_same_namespace name1 name2 =
  if (String.length name1.name_id > 0) && (String.length name2.name_id > 0) then
    (Char.is_uppercase name1.name_id.[0]) = (Char.is_uppercase name2.name_id.[0])
  else true

and lower_compare {name_module = m1; name_id = n1; _}  {name_module = m2; name_id = n2; _} =
  match String.compare (String.lowercase m1) (String.lowercase m2) with
  | 0 -> String.compare (String.lowercase n1) (String.lowercase n2)
  | lg -> lg

and equal ({hash_module = hm1; hash_id = hn1; _} as n1) 
    ({hash_module = hm2; hash_id = hn2; _} as n2) =
  (hn1 = hn2) && (hm1 = hm2) && (lower_compare n1 n2 = 0)

and create_qualified m n = 
  let short s = String.of_char_list @@ List.take (String.to_list @@ String.lowercase s) 4 in
  let hash s = String.fold ~init:0 ~f:(fun h c -> h*256 + (Char.to_int c)) (short s) in
  { name_module = m; hash_module = (hash m); name_id = n; hash_id = (hash n)}

and create s = create_qualified "" s

