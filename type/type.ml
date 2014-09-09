open Name
open Id

(* 
 * types.ml
 * Ported from Daan Leijin's implementation, 
 * which is licensed under the Apache License
 *)

type typ =
  
  (* forall a b c. phi, psi => rho
   * there is at least one variable
   * every variable occurs at least once in rho
   * variables and predicates are canonically ordered
   * each predicate refers to at least one of the variables
   * rho has kind * (wildcard) *)
  | TForAll of typevar list * pred list * rho


  (* (x:a, y:b, z:c) -> m d *)
  | TFun of ((name * typ) list) * effect * typ

  (* a type constant (primitive, label, or newtype; not -> or => *)
  | TCon of typecon

  (* type variable (cannot instantiate to -> or =>) *)
  | TVar of typevar

  (* application of datatypes *)
  | TApp of typ * typ list

  (* type synonym indirection
   * first (type list) is the actual arguments 
   * final typ is the "real" type (expanded) (it always has kind '*' ) *)
  | TSyn of typesyn * typ list * typ

and pred = 
  | PredSub   of typ * typ
  | PredIFace of name * typ list

(* Various synonyms of types *)
and scheme = typ
and sigma  = typ                (* polymorphic type *)
and tau    = typ                (* monomorphic type *)
and rho    = typ                (* unqualified type *)
and effect = tau

(* An inference type can contain type variables of flavour 'Meta' or 'Skolem' *)
and infertype = typ

(* Type variables are variables in a type and contain an identifier and
 * kind. One can ask for the free type variables in a type, and substitute
 * them with 'tau' types. *)
and typevar = 
  {
    typevarId      : id;
    typevarKind    : kind;
    typevarFlavour : flavour; 
  }
  
(* The flavour of a type variable. Types in a 'Type.assumption' (gamma) and inferred types in "Core.core"
 * are always the flavour of the 'Bound' flavour. 'Meta' and 'Skolem' type variables only ever occur 
 * during type inference. *)
and flavour = Meta | Skolem | Bound

(* Type constants have a name and a kind *)
and typecon = 
  {
    typeconName : name;
    typeconKind : kind; 
  }

(* Type synonyms have an identifier, kind, and rank (= partial ordering among type synonyms) *)
and typesyn = 
  {
    typesynName : name;
    typesynKind : kind;
    typesynRank : synonymrank;
    typesynInfo : syninfo option;
  }

(* The rank of a type synonym gives a relative ordering among them. This is used
 * during unification to increase the chance of matching up type synonyms. *)
and synonymrank = int


let rec max_synonym_rank = function 
  | TForAll(_,_,rho)  -> max_synonym_rank rho
  | TFun(args,eff,tp) -> max_synonym_ranks @@ tp::eff::(List.map snd args)
  | TCon _            -> 0
  | TVar _            -> 0
  | TApp(tp,tps)      -> max_synonym_rank tp::tps
  | TSyn(syn,args,tp) -> max (synonym_rank syn) (max_synonym_ranks tp::args)

and max_synonym_ranks tps = 
  List.fold_right max (List.map max_synonym_rank tps) 0
