module type EQ_B =
sig
  type a
  val eq: a -> a -> bool
end

module type ORD_B =
sig
  include EQ_B
  val lt: a -> a -> bool
end

module EQ (M : EQ_B) = struct
  include M
  let neq x y = not(eq x y)
  let member (y:a) (xs : a list) =
  let rec helper xs = match xs with
    | [] -> false
    | x::xs -> if (eq x y) then true else  helper xs in
    helper xs
end

module ORD (M : ORD_B) = struct
  include M
  let leq x y = (lt x y) || (eq x y)
  let max (xs : a list) =
  let rec helper xs = match xs with
    | [] -> failwith "[] for max argument"
    | [x] -> x
    | x::xs -> let y=helper xs in
	if lt x y then x else y in
    helper xs
end

  
module I_Int_EQ_B = struct
  type a = int
  let eq = (=)
end
  
module I_Int_EQ = EQ(I_Int_EQ_B)



module I_Int_ORD_B = struct
  include I_Int_EQ_B
  let lt = (<)
end

module I_Int_ORD = ORD(I_Int_ORD_B)

