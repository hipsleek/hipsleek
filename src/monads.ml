#include "xdebug.cppo"
open Typeclass

(* module for typevar t *)
module type TypeVar = sig type t end


(* module for typevar t2 *)
module type TypeVar2 = sig type t2 end

(* monad m basics *)
module type Monad_B = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end


(* monad m with extensions *)
module Monad_E (M : Monad_B) = struct
  open M 
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

module Monad (M : Monad_B) = struct
  include M 
  include Monad_E(M)
end

(* instance state monad basic *)
module StateM_B (S : TypeVar) = struct
  include S
  type 'a m = S.t -> 'a * S.t
  let return a = (fun s -> (a, s))
  let bind (m) f = (fun s ->
      let (x, s') = m s in f x s')
end


(* instance state monad extension *)
module StateM_E(S : sig
                  type t
                  type 'a m = t -> 'a * t end) = 
struct
  let get = (fun s -> (s, s))
  let put s = (fun _ -> ((), s))
  (* evaluate and get value *)
  let eval (m) = fun s -> fst (m s)
  (* run and get state *)
  let run  (m) = fun s -> snd (m s)
end

(* instance state monad with everything *)
module StateM(S : TypeVar)  = struct
  include Monad (StateM_B(S))
  include StateM_E(StateM_B(S))
end

(* instantiating int for t *)
module Int4t = struct type t = int end

(* instance state monad with int for t *)
module StateM_int = StateM(Int4t)

let incr = StateM_int.bind StateM_int.get (fun s -> StateM_int.put (succ s))

let ( +! ) mx my =
  StateM_int.bind mx (fun x ->
      StateM_int.bind my (fun y -> 
          StateM_int.bind incr (fun _ -> 
              StateM_int.return (x + y))))

(* to implement List Monad - MonadPlus*)

module type MonadPlus_B = sig
  type 'a m
  val zeroM : 'a m
  val plusM : 'a m -> 'a m -> 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end


(* instance state monad basic *)
module MonadList_B  = struct
  type 'a m = 'a list
  let return a = [a]
  let zeroM = []
  let plusM x y = x@y
  let bind m f = List.concat (List.map f m)
end


(* to implement Option Monad *)
module MonadOption_B  = struct
  type 'a m = 'a option
  let return a = Some a
  let bind m f = match m with
    | None -> None
    | Some v -> f v
end

(* instance state monad with everything *)
module MonadList  = Monad (MonadList_B)

(* instance state monad with everything *)
module MonadOption  = Monad (MonadOption_B)

(* to implement Error Monad *)
module type MonadErr_B_sig = sig
  type 'a m = Success of 'a | Error of string
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module MonadErr_B = struct
  type 'a m = Success of 'a | Error of string
  let return a = Success a
  let bind er f = match er with
    | Success v -> f v
    | Error s -> Error s
end


module MonadErr_E (M:MonadErr_B_sig) (S:SHOW_B) = struct
  module A=SHOW(S)
  let showE e = match e with
    | (M.Success v) -> "Value: "  ^(A.show v) 
    | (M.Error s) -> "Error: "^s
end

(* maybe below can replace MonadErr_E *)
module MonadErr_E2 (S:SHOW_B) = struct
  include MonadErr_B
  module A=SHOW(S)
  let showE e = match e with
    | (Success v) -> "Value: "  ^(A.show v) 
    | (Error s) -> "Error: "^s
end

module I_Show_B = struct
  module M = MonadErr_B
  type s = ENum of int | EFun of (s M.m -> s M.m)
  let shows x s = match x with
    | ENum i -> (string_of_int i) ^ s
    | EFun _ -> "a function!"^s
end

module Interp = struct
  module M=MonadErr_E2(I_Show_B)
  open M
end





(* let test (t:eTerm) : string = M.showM (interp t []) *)
