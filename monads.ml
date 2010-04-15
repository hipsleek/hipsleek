module type TypeVar = sig type t end
module XInt = struct type t = int end


module type Monad_B = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end


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

module StateM_B (S : TypeVar) = struct
  include S
  type 'a m = St of (S.t -> 'a * S.t)
  let return a = St (fun s -> (a, s))
  let bind (St m) f = St (fun s ->
			    let (x, s') = m s in
			    let (St m') = f x in
			      m' s')

end



module StateM_E(S : sig
		  type t
		  type 'a m = St of (t -> 'a * t) end) = struct
  let get = S.St (fun s -> (s, s))
  let put = fun s -> S.St (fun _ -> ((), s))
  let eval (S.St m) = fun s -> fst (m s)
  let run  (S.St m) = fun s -> snd (m s)
end

module StateM(S : TypeVar)  = struct
  include Monad (StateM_B(S))
  include StateM_E(StateM_B(S))
    (* include State(S) *)
end

module StateM_i = StateM(XInt)

let incr = StateM_i.bind StateM_i.get (fun s -> StateM_i.put (succ s))
  
let ( +! ) mx my =
  StateM_i.bind mx (fun x -> StateM_i.bind my
		      (fun y -> StateM_i.bind incr (fun _ -> StateM_i.return (x + y))))
    
