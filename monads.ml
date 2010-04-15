(* module to introduce typevar t *)
module type TypeVar = sig type t end

(* module to introduce basics of monad m *)
module type Monad_B = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

(* module for monad m with extensions *)
module Monad (M : Monad_B) = struct
  include M 
  let seq m f = bind m (fun _ -> f)
  let join m = bind m (fun m -> m)
  let fmap f m = bind m (fun x -> return (f x))
  let liftm = fmap
  let liftm2 f m m' =
    bind m  (fun x ->
	       bind m' (fun y ->
			  return (f x y)))
  let liftm3 f m m' m'' =
    bind m   (fun x ->
		bind m'  (fun y ->
			    bind m'' (fun z ->
					return (f x y z))))
  let mapm f l =
    List.fold_right (liftm2 (fun x xs -> f x :: xs)) l (return [])
  let sequence l = mapm (fun x -> x) l
  let mapm_ f l =
    List.fold_right (fun x -> seq (f x)) l (return ())
  let sequence_ l = mapm_ (fun x -> x) l
  let ( >>= ) = bind
  let ( >>  ) = seq
end

(* instance state monad basic wo wrapper *)
module StateM_B (S : TypeVar) = struct
  include S
  type 'a m = (S.t -> 'a * S.t)
  let return a = (fun s -> (a, s))
  let bind (m) f = (fun s ->
			    let (x, s') = m s in
			    let m' = f x in
			      m' s')
end



(* instance state monad with extension *)
module StateM_E(S : sig
		  type t
		  type 'a m = (t -> 'a * t) end) = struct
  let get = (fun s -> (s, s))
  let put = fun s ->  (fun _ -> ((), s))
  let eval (m) = fun s -> fst (m s)
  let run  (m) = fun s -> snd (m s)
end

(* instance state monad with all extensions *)
module StateM(S : TypeVar)  = struct
  include Monad (StateM_B(S))
  include StateM_E(StateM_B(S))
end

module XInt = struct type t = int end

(* instance state monad int *)
module StateM_int = StateM(XInt)

let incr = StateM_int.bind StateM_int.get (fun s -> StateM_int.put (succ s))
  
let ( +! ) mx my =
  StateM_int.bind mx (fun x ->
		      StateM_int.bind my
			(fun y -> StateM_int.bind incr (fun _ -> StateM_int.return (x + y))))
    
