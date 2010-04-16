(* Class EQ Basic *)
module type EQ_B =
sig
  type a
  val eq: a -> a -> bool
end

(* Class ORD Basic *)
module type ORD_B =
sig
  include EQ_B
  val lt: a -> a -> bool
end

(* Class EQ Extended with defaults and other operators *)
module EQ (M : EQ_B) = struct
  (* type "a" imported from M *)
  include M
  let neq x y = not(eq x y)
  let member (y:a) (xs : a list) : bool =
  let rec helper xs = match xs with
    | [] -> false
    | x::xs -> if (eq x y) then true else  helper xs in
    helper xs
end

(* Class ORD Extended with defaults and other operators *)
module ORD (M : ORD_B) = struct
  (* type "a" imported from M *)
  include M
  let leq x y = (lt x y) || (eq x y)
  let gt x y = (lt y x) 
  let geq x y = (leq x y) 
  let max (xs : a list) : a =
  let rec helper xs = match xs with
    | [] -> failwith "[] for max argument"
    | [x] -> x
    | x::xs -> let y=helper xs in
	if lt x y then x else y in
    helper xs
end

  
(* instance Int EQ Base *)
module I_Int_EQ_B = struct
  type a = int
  let eq = (=)
end
  
(* instance Int EQ Extension *)
module I_Int_EQ = EQ(I_Int_EQ_B)

(* instance Int ORD Base *)
module I_Int_ORD_B = struct
  include I_Int_EQ_B
  let lt = (<)
end

(* instance Int ORD Extension *)
module I_Int_ORD = ORD(I_Int_ORD_B)

(* Class Show Basic *)
module type SHOW_B =
sig
  type a
  val shows: a -> string -> string
end

(* Class SHOW Extended with defaults and other operators *)
module SHOW (M : SHOW_B) = struct
  (* type "a" imported from M *)
  include M
  let show (x:a) : string  = shows x ""
end



