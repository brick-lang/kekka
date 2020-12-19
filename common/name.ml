open Core
open Core.Poly
open BasicClasses
open Util

(*********************************
 * Names
 *********************************)
(**
 * Names defined by the user.
 * Uses a hash to speed up comparisons. The hash is constructed
 * such that they can be compared too. (h1 > h2 => name1 > name2)
 * The hash is case-insensitive, just like comparisons on names.
 * Use 'case_equal' for case-sensitive comparisons.
*)
type t =  {
  name_module : string;
  hash_module : int;
  name_id     : string;
  hash_id     : int;
} [@@deriving sexp]

let case_equal name1 name2 =
  (name1.name_module = name2.name_module) &&
  (name1.name_id = name2.name_id)

(* Checks whether both names are in the same namespace *)
let is_same_namespace name1 name2 =
  if (String.length name1.name_id > 0) && (String.length name2.name_id > 0) then
    (Char.is_uppercase name1.name_id.[0]) = (Char.is_uppercase name2.name_id.[0])
  else true

let case_overlap name1 name2 =
  (not @@ case_equal name1 name2) && (is_same_namespace name1 name2)

let lower_compare n1 n2 =
  match String.compare (String.lowercase n1.name_module) (String.lowercase n2.name_module) with
  | 0 -> String.compare (String.lowercase n1.name_id) (String.lowercase n2.name_id)
  | lg -> lg

let equal n1 n2 =
  (n1.hash_id = n2.hash_id) &&
  (n1.hash_module = n2.hash_module) &&
  (lower_compare n1 n2 = 0)

let compare n1 n2 =
  let c1 = Int.compare n1.hash_module n2.hash_module in
  let c2 = Int.compare n1.hash_id n2.hash_id in
  if c1 <> 0 then c1
  else if c2 <> 0 then c2
  else lower_compare n1 n2

let show { name_module = m; name_id = n; _ } =
  if String.is_empty m then
    n
  else
    m ^ "/" ^ (let c = String.get m 0 in (* We're guranteed non-zero length *)
               if not (Char.is_alpha c || c = '_' || c ='(') then
                 "(" ^ n ^ ")"
               else n)

(** Show quotes around the name *)
let pp fmt name = Format.pp_print_string fmt ("\"" ^ (show name) ^ "\"")

let new_qualified m n =
  let string_take i s = s |> String.to_list |> Util.flip (List.take) i |> String.of_char_list in
  let short s = string_take 4 (String.lowercase s) in
  let hash s = String.fold ~init:0 ~f:(fun h c -> h*256 + (Char.to_int c)) (short s) in
  { name_module = m; hash_module = (hash m); name_id = n; hash_id = (hash n)}

let create s = new_qualified "" s

let nil = create ""

let is_nil { name_module = m; name_id = n; _ } = String.is_empty n

let qualify
      ({ name_module = x; name_id = m; hash_id = hm; _} as n1)
      ({ name_module = y; name_id = n; hash_id = hn; _} as n2) =
  if (String.is_empty x && String.is_empty y) ||
     (String.is_empty x && m = y) then
    { name_module = m; hash_module = hm; name_id = n; hash_id = hn }
  else
    failwithf "Common.Name.qualify: Cannot use qualify on qualified names: (%s, %s)" (show n1) (show n2) ()

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
  new_hidden_name ("field" ^ i)

let is_field_name = is_hidden_name

let new_implicit_type_var_name i =
  new_hidden_name ("t" ^  i)

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
  String.to_list s |> split_camel_list |> List.map ~f:String.of_char_list


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
  String.of_char_list @@ List.init (len - (List.length hexs)) ~f:(fun _ -> '0') @ hexs

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
    String.of_char_list @@ (List.map ~f:(fun _ -> '_') dots) @ (List.concat_map ~f:encode_char rest)
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
        | '.'::'c'::'o'::'n'::' '::cs      ->  "_con_" ^ encode_chars (String.of_char_list cs)
        | '.'::'t'::'y'::'p'::'e'::' '::cs ->  "_type_" ^ encode_chars (String.of_char_list cs)
        | _ -> encode_chars name


let module_name_to_path name =
  ascii_encode true (show name)

module Map = struct
  module C = Comparator.Make(struct
      type nonrec t = t
      let compare = compare
      let sexp_of_t = sexp_of_t
    end)
  include Map.Make_using_comparator(struct
      include C
      type nonrec t = t
      let t_of_sexp = t_of_sexp
      let sexp_of_t = sexp_of_t
   end)

  (* left-biased union(s) *)
  let union m1 m2 =
    merge m1 m2 ~f:(fun ~key -> function `Both(l,r) -> Some l | `Left l -> Some l | `Right r -> Some r)

  let rec union_list = function
    | [] -> empty
    | x::[] -> x
    | x::ys -> union x (union_list ys)
end


(***************************************************
 * Primitives (originally in NamePrim) 
 ***************************************************)
let system_core = create "std/core"
let core = create "core"
let prelude_name s = qualify system_core @@ create s

(* Special *)
let expr = create ".expr"
let typ = create ".type"
let interactive_module = create "interactive"
let interactive = create "interactive"
let main = create "main"
let copy = create ".copy"
let op_expr = create ".opexpr"

(* Primitive operations *)
let if_ = create "if"
let case = create "case"
let unit = create "()"
let pred_heap_div = prelude_name "hdiv"
let return = prelude_name ".return"
let trace = prelude_name "trace"
let log = prelude_name "log"
let effect_open = create ".open"

(* Primitive constructors *)
let true_ = prelude_name "True"
let false_ = prelude_name "False"

let just = prelude_name "Just"
let nothing = prelude_name "Nothing"

let optional = prelude_name "Optional"
let optional_none = prelude_name "None"
let tp_optional = prelude_name "optional"

(* Lists *)
let null = prelude_name "Nil"
let cons = prelude_name "Cons"
let enum_from_to = prelude_name "enumFromTo"
let enum_from_then_to = prelude_name "enumFromThenTo"
let tp_list = prelude_name "list"

(* Primitive type constructors *)
let effect_empty = prelude_name "<>"
let effect_extend = prelude_name "<|>"
let effect_append = create ".<+>"

let tp_bool    = prelude_name "bool"
let tp_int     = prelude_name "int"
let tp_float   = prelude_name "double"
let tp_char    = prelude_name "char"
let tp_string  = prelude_name "string"
let tp_any     = prelude_name "any"

let tp_io      = prelude_name "io"
let tp_unit    = prelude_name "()"
let tp_ref     = prelude_name "ref"
let ref_       = prelude_name "ref"

let tp_total   = prelude_name "total"
let tp_partial = prelude_name "exn"
let tp_div     = prelude_name "div"
let tp_pure    = prelude_name "pure"

let tp_alloc   = prelude_name "alloc"
let tp_read    = prelude_name "read"
let tp_write   = prelude_name "write"
let tp_st      = prelude_name "st"

let tp_void    = prelude_name "void"

let tp_async   = prelude_name "async"
let tp_exception = prelude_name "exception"


let tuple n = prelude_name ("(" ^ String.make (n - 1) ',' ^ ")")
(* let%test _ = String.equal "()" (tuple 1).name_id
 * let%test _ = String.equal "(,,,)" (tuple 4).name_id *)

let is_tuple (name : t) =
  let s = String.to_list name.name_id in
  (name.name_module) = (system_core.name_id) &&
  (List.length s) >= 2 &&
  (List.hd_exn s) = '(' && (List.last_exn s) = ')' &&
  List.for_all ~f:((=) ',') (List.tl_exn (List.rev @@ List.tl_exn @@ List.rev s))

(* let%test _ = is_tuple { name_module = system_core.name_id;
 *                         name_id = "(,,,,,,,)";
 *                         hash_id = 0; hash_module = 0 } *)

let to_short_module_name (name:t) : t =
  let short = List.hd_exn @@ List.rev @@ split_module_name name in
  if equal short core then system_core else short

(* Primitive kind constructors *)
let kind_star = create "V"
let kind_label = create "X"
let kind_fun = create "->"
let kind_pred = create "P"
let kind_effect = create "E"
let kind_heap = create "H"
