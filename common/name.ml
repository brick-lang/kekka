open Core.Std
open BasicClasses

(* let implode = List.fold_right ~init: "" ~f:(fun c cs -> (Char.to_string c) ^ cs) *)
let implode l =
  let result = String.create (List.length l) in
  let rec imp i = function
    | [] -> result
    | c :: l -> result.[i] <- c; imp (i + 1) l in
  imp 0 l;;

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
type name =  {
  name_module : string;
  hash_module : int;
  name_id     : string;
  hash_id     : int;
}

implicit 
module Eq_name = struct
  type t = name
  let equal x y =
    (String.equal x.name_module y.name_module) &&
    (x.hash_module = y.hash_module) &&
    (String.equal x.name_id y.name_id) &&
    (x.hash_id = y.hash_id)
       
end

let sexp_of_name n =
  let open Sexplib in
  let sp = sexp_of_pair in
  let ss = sexp_of_string in
  let si = sexp_of_int in
  sexp_of_list Fn.id ([
      sp ss ss ("name_module", n.name_module);
      sp ss si ("hash_module", n.hash_module);
      sp ss ss ("name_id", n.name_id);
      sp ss si ("hash_id", n.hash_id)
    ])

let name_of_sexp s =
  let open Sexplib in
  let ps = pair_of_sexp in
  let ss = string_of_sexp in
  let is = int_of_sexp in
  let a = array_of_sexp Fn.id s in
  {
    name_module = snd (ps ss ss a.(0));
    hash_module = snd (ps ss is a.(1));
    name_id     = snd (ps ss ss a.(2));
    hash_id     = snd (ps ss is a.(3));
  }

type names = name list

let name_case_equal
      { name_module = m1; name_id = n1; _ }
      { name_module = m2; name_id = n2; _ }
  =
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
  match String.compare (String.lowercase m1) (String.lowercase m2) with
  | 0 -> String.compare (String.lowercase n1) (String.lowercase n2)
  | lg -> lg

let eq_name
      ({ hash_module = hm1; hash_id = hn1; _ } as n1)
      ({ hash_module = hm2; hash_id = hn2; _ } as n2) =

  (hn1 = hn2) && (hm1 = hm2) && (lower_compare n1 n2 = 0)

let compare_name
      ({ hash_module = hm1; hash_id = hn1; _ } as n1)
      ({ hash_module = hm2; hash_id = hn2; _ } as n2) =
  match Int.compare hm1 hm2 with
  | 0 -> (match Int.compare hn1 hn2 with
      | 0 -> lower_compare n1 n2
      | lg -> lg)
  | lg -> lg

let show_name { name_module = m; name_id = n; _ } =
  if String.is_empty m
  then n
  else m ^ "/" ^
       let c = String.get m 0 in (* We're guranteed non-zero length *)
       if not (Char.is_alpha c || c = '_' || c ='(') then
         "(" ^ n ^ ")"
       else n

(** Show quotes around the name *)
let pp_name fmt name = Format.pp_print_string fmt ("\"" ^ (show_name name) ^ "\"")

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
      (show_name n1) (show_name n2) ()

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
  else List.map ~f:create @@ String.split ~on:'/' (show_name name)

let unsplit_module_name xs =
  create @@ String.concat ?sep:(Some "/") (List.map ~f:show_name xs)


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

(* let new_field_name i = *)
(*   new_hidden_name ("field" ^ (show i)) *)

let is_field_name = is_hidden_name

(* let new_implicit_type_var_name i = *)
(*   new_hidden_name ("t" ^ (show i)) *)

let is_implicit_type_var_name = is_hidden_name

(* let new_hidden_external_name name = *)
(*   new_hidden_name ((show name) ^ "@extern") *)

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
  String.to_list s |> split_camel_list |> List.map ~f:implode


let camel_to_dash s =
  match List.map ~f:String.lowercase (split_camel s) with
  | x::xs -> List.fold_left ~init:x ~f: (fun y ys -> y ^ "-" ^ ys) xs
  | [] -> ""

(**************************************************
 * name to file path
 **************************************************)

let show_hex len i =
  let show_hex_char = function
    | d when d <= 9 -> Char.of_int_exn (d + Char.to_int '0')
    | d             -> Char.of_int_exn (d - 10 + Char.to_int '0')
  in
  let rec hex_digits i =
    let d = i / 16 in
    let m = i % 16 in
    if d = 0 then [m]
    else m::(hex_digits d)
  in
  let hexs = List.map ~f:show_hex_char (List.rev @@ hex_digits i) in
  implode @@ List.init (len - (List.length hexs)) ~f:(fun _ -> '0') @ hexs

(**************************************************
 * Ascii encode a name
 * - on module names  '/' becomes '_'
 * - on normal names '.' becomes '_' name to file path
 **************************************************)

let ascii_encode is_module name =
  let encode_char c =
    if Char.is_alphanum c then [c]
    else String.to_list @@ match c with
      | '/' when is_module -> "_"
      | '.' when not is_module -> "_"
      | '_' -> "__"
      | '.' -> "_dot_"
      | '-' -> "_dash_"
      | '+' -> "_plus_"
      | '*' -> "_star_"
      | '&' -> "_amp_"
      | '~' -> "_tilde_"
      | '!' -> "_excl_"
      | '@' -> "_at_"
      | '#' -> "_hash_"
      | '$' -> "_dollar_"
      | '%' -> "_perc_"
      | '^' -> "_hat_"
      | '=' -> "_eq_"
      | ':' -> "_colon_"
      | '<' -> "_lt_"
      | '>' -> "_gt_"
      | '[' -> "_lb_"
      | ']' -> "_rb_"
      | '?' -> "_ques_"
      | '/' -> "_fs_"
      | '\\'-> "_bs_"
      | '(' -> "_lp_"
      | ')' -> "_rp_"
      | ',' -> "_comma_"
      | ' ' -> "_space_"
      | '\'' -> "_sq_"
      | '\"' -> "_dq_"
      | '`'  -> "_bq_"
      | '{'  -> "_lc_"
      | '}'  -> "_rc_"
      | _ -> "_x" ^ show_hex 2 (Char.to_int c) ^ "_"
  in
  let encode_chars s =
    let (dots,rest) = List.split_while ~f:(fun c -> c = '.') (String.to_list s) in
    implode @@ (List.map ~f:(fun _ -> '_') dots) @ (List.concat_map ~f:encode_char rest)
  in
  if String.length name > 0 && Char.is_alphanum (String.get name 0) then
    encode_chars name
  else match name with
    | "" -> "_null_"
    | ".<>"   -> "_Total_"
    | ".<|>"  -> "_Extend_"
    | ".()"   -> "_Unit_"
    | ".(,)"  -> "_Tuple2_"
    | ".(,,)" -> "_Tuple3_"
    | ".(,,,)"-> "_Tuple4_"
    | "()"    -> "_unit_"
    | "(,)"   -> "_tuple2_"
    | "(,,)"  -> "_tuple3_"
    | "(,,,)" -> "_tuple4_"
    | "[]"    -> "_index_"
    | _       ->
        (* I hate OCaml string matching so much *)
        match String.to_list name with
        | '.'::'c'::'o'::'n'::' '::cs ->
            (* trace ("con name: " ^ name) .. *) (* For debugging *)
            "_con_" ^ encode_chars (implode cs)
        | '.'::'t'::'y'::'p'::'e'::' '::cs ->
            "_type_" ^ encode_chars (implode cs)
        | _ -> encode_chars name


let module_name_to_path name =
  ascii_encode true (show_name name)
