#include "xdebug.cppo"
open Monads
open Typeclass



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

module MonadErr (S:SHOW_sig) = struct
  include MonadErr_B
  let showE e = match e with
    | (Success v) -> "Value: "  ^(S.show v) 
    | (Error s) -> "Error: "^s
end

module MonadState_B  = struct
  module E=MonadErr_B
  type 'a m = (int -> ('a E.m * int)) 
  let return a =  (fun s -> ((E.return a),s) )
  let bind (m1) k = (fun s ->
		       let (e1,s1) = m1 s in
			 match e1 with
			   | (E.Success v) -> let m2 = k v in (m2 s1)
			   | (E.Error s) -> (E.Error s,s1)
  		    )
end


module MonadState_E (S:SHOW_sig) = struct
  include MonadState_B
  module EX=MonadErr(S) 
  let bind1 m k = bind m (fun _ -> k)
  let errorM m = fun s -> (E.Error m, s)

   let showM m = let (a,s) = m 0 in
    EX.showE a (*^"  ; "^" Count: " ^ (B.show s)	 *)   
  let tickS () : unit m = fun s -> (E.Success (),s+1)
end

    
(* module MonadM_B(S:SHOW_B)  = struct *)
(*   module E=MonadE_B(S) *)
(*   module B=SHOW(S)   *)
(*   type 'a m = (int -> ('a E.m * int))  *)
(*   let return a =  (fun s -> ((E.return a),s) ) *)
(*   let bind (m1) k = (fun s -> *)
(* 		       let (e1,s1) = m1 s in *)
(* 			 match e1 with *)
(* 			   | (E.Success v) -> let m2 = k v in (m2 s1) *)
(* 			   | (E.Error s) -> (E.Error s,s1) *)
(*   		    ) *)
(*   let bind1 m k = bind m (fun _ -> k) *)
(*   let errorM m = fun s -> (E.Error m, s) *)

(*    let showM m = let (a,s) = m 0 in *)
(*     E.showE a (\*^"  ; "^" Count: " ^ (B.show s)	 *\)    *)
(*   let tickS () : unit m = fun s -> (E.Success (),s+1) *)

(* end *)


module I_EV_SHOW_B = struct
  type s = int 				(* Evalue.a *)
  let shows = fun x s -> (string_of_int x) ^ s
end    

module I_SHOW_B = struct
  module M = MonadState_B
  type s = ENum of int | EFun of (s M.m -> s M.m)
  let shows x s = match x with
    | ENum i -> (string_of_int i) ^ s
    | EFun _ -> "<function>"^s
  let show (x:s) : string  = shows x ""
end

module I_SHOW_B2 = struct
  module M = MonadState_B
  type s = ENum of int | EFun of (s M.m -> s M.m)
  let shows x s = match x with
    | ENum i -> (string_of_int i) ^ s
    | EFun _ -> "<function>"^s
end

(* below exposes the Show s type *)
module I_SHOW_B3 = struct 
  include I_SHOW_B2
  include SHOW_E(I_SHOW_B2)
end

module Evalue =  struct
  (* module M=MonadM_B(I_EV_SHOW_B) *)
  module S=I_SHOW_B3
  (* module S=SHOW(I_SHOW_B2) *)
  module M=MonadState_E(SHOW(S))
 
  (* type s = ENum of int | EFun of (s  M.m -> s  M.m) *)
    
  (* let shows v s= match v with *)
  (*     ENum i -> (string_of_int i) ^ s *)
  (*   | EFun f -> "<function>" ^s *)
  (* let show (v) : string = shows v "" *)

    
  type environment = (string * (S.s  M.m)) list

  let rec lookup (n:string) (ev:environment) : S.s M.m =
    match ev with
	[] -> M.errorM ("unbound variable: "^n)
      |(e,v)::evs -> if n=e then v else (lookup n evs)

  let add (x:S.s) (y:S.s) : S.s M.m =
    match (x,y) with
  	((S.ENum i),(S.ENum j)) -> M.bind1 (M.tickS ()) (M.return (S.ENum (i+j)))
      |  _ -> M.errorM ("should be numbers: ")

  let apply (x:S.s) (y: S.s M.m) : S.s M.m =
    match x with
	(S.EFun k) -> M.bind1 (M.tickS ()) (k y)
      | _ -> M.errorM ("should be function: "^ S.show x)
	  
  type eTerm = EVar of string | ECon of int
	       | EAdd of eTerm * eTerm
	       | ELam of string * eTerm
	       |EApp of eTerm * eTerm
		   
  let rec interp (t:eTerm) (ev:environment) : S.s M.m =
    match t with
      | (EVar x) -> lookup x ev
      | (ECon i) -> M.return (S.ENum i)
      | (EAdd (u,v)) -> M.bind (interp u ev) (fun a -> (M.bind (interp v ev) (fun b -> (add a b))))
      | (ELam (x,v)) -> M.return (S.EFun (fun a -> interp v ((x,a)::ev)))
      | EApp (u,v) -> M.bind (interp u ev) (fun a -> (apply a (interp v ev)))

 
  let test (t:eTerm) : string = M.showM (interp t [])

   (*let () = print_string ("\n" ^ (test (ECon 2)) ^"\n");print_string ("\n" ^ (test (EApp ((ECon 2),(ECon 2)))) ^"\n")*)
       
     
end




  




    
