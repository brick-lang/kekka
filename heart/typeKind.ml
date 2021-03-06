open Common

(*********************************
   Get the kind of a type
 *********************************)

(* Soooo, in the original source, this is done with a HasKind typeclass. 
 * But I _really_ don't want to deal with OCaml's functors, since it'll just
 * introduce _more_ complexity to the already-weird module layout. So instead,
 * we're going to continue ppx_deriving's convention of prefixes and then types.
 * a la get_kind_kind. *)

module type HasKind = sig
  type t
  val get_kind : t -> Kind.t
end


let get_kind_kind k = k
let get_kind_type_var { Type.TypeVar.kind = k; _ } = k
let get_kind_type_con { Type.TypeCon.kind = k; _ } = k
let get_kind_type_syn { Type.type_syn_kind = k; _ } = k
let rec get_kind_typ =
  let rec collect acc = function
    | Kind.App(Kind.App(arr,k1),k2) when arr = Kind.Prim.arrow -> collect (k1::acc) k2
    | k -> k :: acc
  in
  let rec kind_apply l k =
    match (l,k) with
    | [], _ -> k
    | (_::rest), Kind.App(Kind.App(arr,k1),k2) -> kind_apply rest k2
    | _,_ -> Core.failwithf "TypeKind.t_apply: illegal kind in application? %s" (Kind.show k) ()
  in
  let open Type in function
    | TForall(_,_,tp) -> get_kind_typ tp
    | TFun _          -> Kind.Prim.star
    | TVar v          -> get_kind_type_var v
    | TCon c          -> get_kind_type_con c
    | TSyn(syn,xs,tp) -> (*getKind tp (* this is wrong for partially applied type synonym arguments, see "kind/alias3" test *)*)
        kind_apply xs (get_kind_type_syn syn)
    | TApp(tp,args)   -> begin
        match collect [] (get_kind_typ tp) with
        | (kres::_) -> kres
        | _ -> Core.failwithf "TypeKind: illegal kind in type application? %s" (Kind.show @@ get_kind_typ tp) ()
      end
