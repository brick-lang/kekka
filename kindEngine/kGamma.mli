open Common
open Heart

type t = Kind.t QNameMap.t
val empty : t
val single : Name.t -> Kind.t -> t
val create : (Name.t * Kind.t) list -> t
val new_dedup : (Name.t * Kind.t) Util.List.t -> t
val extend : name:Name.t -> data:Kind.t -> t -> t
val lookup : Name.t -> Name.t -> t -> Kind.t QNameMap.lookup
val lookup_q : Name.t -> t -> Kind.t option
val find : Name.t -> Name.t -> t -> Name.t * Kind.t
val to_list :t -> (Name.t * Kind.t) Util.List.t
val filter : Name.t -> t -> t
val union : t -> t -> t
val union_list : t list -> t
val init : t
val is_empty : t -> bool
