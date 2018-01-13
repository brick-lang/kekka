include Core.Fn

let (<.>) f g x = f @@ g x
let (<.:>) f g x y = f @@ g x y
let until p f =
  let rec go = function
    | x when p x -> x
    | x -> go @@ f x
  in go


(* Implementation of arrows for functions *)
let (<<<) f g x = f @@ g x
let (>>>) f g x = g @@ f x
let arr f = f    
let ( *** ) f g (x,y) = (f x, g y)
let first f = f *** id
let second f = id *** f
let (&&&) f g  = arr (fun b -> (b,b)) >>> f *** g
let return = id
let (<<^) a f = a <<< arr f
let (^<<) a f = arr f <<< a
let (^>>) a f = arr f >>> a
let (>>^) a f = a >>> arr f

module List = struct
  include Core.List
  let guard = function
    | true -> return ()
    | false -> []
end
