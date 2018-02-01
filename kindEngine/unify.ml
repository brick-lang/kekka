open Core
open InferKind

type t =
  | Ok of KSub.t
  | InfiniteKind
  | NoMatch

type context =
  | Check of string (* * range *)
  | Infer (* of range *)

(* TODO: replace this with Kind.equal *)
let rec match_kind k1 k2 = let open Heart.Kind in match k1,k2 with
  | Constant(c1), Constant(c2) -> Common.Name.equal c1 c2
  | App(k1, k2), App(l1, l2) -> match_kind k1 l1 && match_kind k2 l2
  | _ -> false

let unify_var id kind =
  if KVs.member id (InfKind.fkv kind) then
    InfiniteKind
  else Ok (KSub.single id kind)


(* TODO: What the heck does 'mgu' stand for? something something unify? *)
let rec mgu ik1 ik2 = 
  let open InfKind in
  match ik1,ik2 with
  | Var(id1), Var(id2) when id1 = id2 -> Ok KSub.empty
  | Con(k1),  Con(k2) -> if match_kind k1 k2 then Ok KSub.empty else NoMatch
  | App(k1,k2), App(l1,l2) -> begin
      match mgu k1 l1 with
      | Ok(sub1) -> begin
          match mgu InfKind.(sub1 |=> k2) InfKind.(sub1 |=> l2) with
          | Ok(sub2) -> Ok KSub.(sub2 @@@ sub1)
          | err -> err
        end
      | err -> err
    end

  (* pull up Applications *)
  | Con(App(k1,k2)), App(l1,l2) -> mgu (App(Con k1, Con k2)) (App(l1, l2))
  | App(k1,k2), Con(App(l1,l2)) -> mgu (App(k1, k2)) (App(Con l1, Con l2))

  (* unify variables *)
  | Var(id), kind -> unify_var id kind
  | kind, Var(id) -> unify_var id kind

  (* no match *)
  | _ -> NoMatch

let kind_error context err kind1 kind2 =
  let message = match err with
    | InfiniteKind -> "Invalid type (due to an infinite kind)\n"
    | _            -> "Invalid type\n"
  in 
  let expected = match context with
    | Check msg -> Format.sprintf " because %s" msg
    | Infer     -> ""
  in 
  failwithf "%sinferred kind: %s\nexpected kind:%s%s" message expected (InfKind.show kind1) (InfKind.show kind2) ()

let unify (context:context) (kind1:InfKind.t) (kind2:InfKind.t) = let open InferMonad in
  let%bind skind1 = subst kind1 in
  let%bind skind2 = subst kind2 in
  match mgu skind1 skind2 with
  | Ok(sub') -> extend_ksub sub'
  | err      -> kind_error context err skind1 skind2
                           
  
