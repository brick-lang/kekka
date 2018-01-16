(** Identity function  *)
let id x = x 

(** Constant function *)
let const x _ = x
let seq  _ x = x

(** Flip takes its (first) two arguments in the reverse order of f *)
let flip f x y = f y x
let flip2 f y z x = f x y z
let flip3 f x y z w = f w x y z

module type Monad = sig
  type 'a t
  val map    : 'a t -> f:('a -> 'b) -> 'b t
  val return : 'a -> 'a t
  val bind   : 'a t -> f:('a -> 'b t) -> 'b t
end

module type S = sig
  include Monad

  (* Functorial things *)
  val fmap : ('a -> 'b) -> 'a t -> 'b t

  val (<$)  : 'a -> 'b t -> 'a t
  val ($>)  : 'a t -> 'b -> 'b t
  val (<$>) : ('a -> 'b) -> 'a t -> 'b t
  val (<$$>) : 'a t -> ('a -> 'b) -> 'b t

  val ($<<) : 'a -> 'b -> 'a t
  val ($<) : 'a t -> 'b -> 'a t
  val (>>$) : 'a -> 'b -> 'b t
  val (>$) : 'a -> 'b t -> 'b t
  val ($>=) : 'a -> ('a -> 'b t) -> 'b t

  (* Applicative things *)
  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t
  val ( *> ) : 'a t -> 'b t -> 'b t
  val ( <* ) : 'a t -> 'b t -> 'a t

  val ( <**> ) : 'a t -> ('a -> 'b) t -> 'b t

  (* Monadic things *)
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (=<<)   : ('a -> 'b t) -> 'a t -> 'b t
  val (>>)  : 'a t -> 'b t -> 'b t

  val fail : string -> 'a t
  val join : 'a t t -> 'a t
  val ignore : 'a -> unit t

  val sequence : 'a t list -> 'a list t
  val sequence_ : 'a t list -> unit t
  val mapM : ('a -> 'b t) -> 'a list -> 'b list t
  val mapM_ : ('a -> 'b t) -> 'a list -> unit t
  val filterM : ('a -> bool t) -> 'a list -> 'a list t
  val forM : 'a list -> ('a -> 'b t) -> 'b list t
  val forM_ : 'a list -> ('a -> 'b t) -> unit t
  val forever : 'a t -> 'b t
  val void : 'a t -> unit t
  val foldM : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
  val foldM_ : ('a -> 'b -> 'a t) -> 'a -> 'b list -> unit t
  val replicate : int -> 'a -> 'a list
  val replicateM : int -> 'a t -> 'a list t
  val replicateM_ : int -> 'a t -> unit t
  val mwhen : bool -> unit t -> unit t
  val unless : bool -> unit t -> unit t
  val liftM : ('a -> 'b) -> 'a t -> 'b t
  val liftM2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val liftM3 : ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
  val liftM4 :
    ('a -> 'b -> 'c -> 'd -> 'e) -> 'a t -> 'b t -> 'c t -> 'd t -> 'e t
  val ap : ('a -> 'b) t -> 'a t -> 'b t
end

module Make(M : Monad) : S with type 'a t = 'a M.t = struct
  include M

  let pure = return

  let (>>=) a f = bind a ~f
  let fmap f a = map ~f a

  let (<$) x = fmap (const x)
  let ($>) x y = y <$ x
  let (<$>) = fmap
  let (<$$>) x y = fmap y x

  let (>$) x = fmap (seq x)
  let ($<) x y = y >$ x
  let (>>$) x y = (return x) $> y
  let ($<<) x y = y >>$ x

  let ($>=) x y = (return x) >>= y

  let liftM  f m     = m  >>= fun x  -> return (f x)
  let liftM2 f m1 m2 = m1 >>= fun x1 -> m2 >>= fun x2 -> return (f x1 x2)

  let (<*>) fs xs = fs >>= fun f -> xs >>= fun x -> return (f x)

  (** Sequence actions, discarding the value of the first argument *)
  let ( *> ) a1 a2 = (id <$ a1) <*> a2

  (** Sequence actions, discarding the value of the second argument.  *)
  let ( <* ) a b = liftM2 const a b

  (** A variant of '<*>' with the arguments reversed. *)
  let (<**>) a b = liftM2 (flip (@@))  a b

  (* Sequential composition of two actions, discarding any value produced
   * by the first. Similar to semicolon normally. *)
  let (>>) m k = m >>= fun _ -> k

  let fail s = failwith s
  let join x = x >>= id

  (* Jane Street's 'map' is really '<$$>' *)
  let (>>|) = (<$$>)
  (* let ($$>) x y = (return x) $>> y *)

  let ignore t = return ()

  let (=<<) x y = y >>= x

  let sequence ms =
    let k m n =
      m >>= fun x ->
      n >>= fun xs ->
      return (x::xs)
    in
    List.fold_right k ms (return [])

  let sequence_ ms =
    List.fold_right (>>) ms (return ())

  let mapM  f a = sequence  (List.map f a)
  let mapM_ f a = sequence_ (List.map f a)

  let rec filterM p = function
    | []    -> return []
    | x::xs ->
        p x >>= fun flg ->
        filterM p xs >>= fun ys ->
        return (if flg then x::ys else ys)

  let forM  x y = mapM  y x
  let forM_ x y = mapM_ y x

  let forever a = let rec b () = a >> b () in b ()
  let void m = fmap (const ()) m

  let rec foldM f a = function
    | []    -> return a
    | x::xs -> f a x >>= fun fax -> foldM f fax xs

  let foldM_ f a xs = foldM f a xs >> return ()

  let rec replicate n i =
    match n with
    | 0 -> []
    | _ -> i::(replicate (n - 1) i)

  let replicateM n x = sequence (replicate n x)
  let replicateM_ n x = sequence_ (replicate n x)

  let mwhen p s = if p then s else return ()
  let unless p s = if p then return () else s

  let liftM3 f m1 m2 m3 = m1 >>= fun x1 -> m2 >>= fun x2 -> m3 >>= fun x3 -> return (f x1 x2 x3)
  let liftM4 f m1 m2 m3 m4 = m1 >>= fun x1 -> m2 >>= fun x2 -> m3 >>= fun x3 -> m4 >>= fun x4 -> return (f x1 x2 x3 x4)
  let ap       m1 m2 = liftM2 id m1 m2
end
