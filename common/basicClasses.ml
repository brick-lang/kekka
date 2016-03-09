
module type Eq = sig
  type t
  val equal  : t -> t -> bool
end

let equal {E:Eq} x y = E.equal x y

module type Ord = sig
  type t 
  module Eq : Eq with type t = t
  val compare : t -> t -> int
end

let compare {O:Ord} x y = O.compare x y

module type Show = sig
  type t
  val show : t -> string
end

let show {S:Show} x = S.show x

