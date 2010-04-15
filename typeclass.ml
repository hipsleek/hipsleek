module type EQ_m =
sig
  type a
  val eq: a -> a -> bool
end

module type ORD_m =
sig
  include EQ_m
  val lt: a -> a -> bool
end

module EQ_E (M : EQ_m) = struct
  include M
  let neq x y = not(eq x y)
  let member (y:a) (xs : a list) =
  let rec helper xs = match xs with
    | [] -> false
    | x::xs -> if (eq x y) then true else  helper xs in
    helper xs
end

module ORD_E (M : ORD_m) = struct
  include M
  let leq x y = (lt x y) || (eq x y)
  let max (xs : a list) =
  let rec helper xs = match xs with
    | [x] -> x
    | x::xs -> let y=helper xs in
	if lt x y then x else y in
    helper xs
end

  
module I_Int_EQ = struct
  type a = int
  let eq = (=)
end
  
module I_Int_EQ_E = EQ_E(I_Int_EQ)



module I_Int_ORD = struct
  include I_Int_EQ
  let lt = (<)
end

module I_Int_ORD_E = ORD_E(I_Int_ORD)

