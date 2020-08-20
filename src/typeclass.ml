#include "xdebug.cppo"
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
module EQ_E (M : EQ_B) = struct
  (* type "a" imported from M *)
  open M
  let neq x y = not(eq x y)
  let member (y:a) (xs : a list) : bool =
    begin
      let rec helper xs = match xs with
        | [] -> false
        | x::xs -> if (eq x y) then true else  helper xs in
      helper xs
    end
end


module EQ (M : EQ_B) = struct
  (* type "a" imported from M  but abstract *)
  include M
  include EQ_E(M)
end

(* instance (Eq a, Eq b) => Eq (a,b)
   eq (x1,y1) (x2,y2) = (eq x1 x2) & (eq y1 y2)
*)
module TUPLE_EQ_B (M1 : EQ_B) (M2 : EQ_B) = struct
  type a = (M1.a * M2.a)
  let eq (x1,x2) (y1,y2) = (M1.eq x1 y1) && (M2.eq x2 y2)
end

(* instance Eq a => Eq [a]
   eq [] [] = true
   eq (x:xs) (y:ys) = (eq x y) && (eq xs ys)
   eq _ _ = false
*)
module LIST_EQ_B (M : EQ_B) = struct
  type a = M.a list
  let rec eq xs ys = match xs,ys with
    | [], [] -> true
    | (x::xs), (y::ys) -> (M.eq x y) && (eq xs ys)
    | _, _ -> false
end

(* Class ORD Extended with defaults and other operators *)
module ORD_E (M : ORD_B) = struct
  (* type "a" imported from M *)
  open M
  let leq x y = (lt x y) || (eq x y)
  let gt x y = (lt y x) 
  let geq x y = (leq x y) 
  let max (xs : a list) : a =
    begin
      let rec helper xs = match xs with
        | [] -> failwith "[] for max argument"
        | [x] -> x
        | x::xs -> let y=helper xs in
          if lt x y then x else y in
      helper xs
    end
end

module ORD (M : ORD_B) = struct
  (* type "a" imported from M *)
  include M
  include ORD_E(M)
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
  type s
  val shows: s -> string -> string
end

module type SHOW_sig =
sig
  type s
  val shows: s -> string -> string
  val show: s -> string
end

module SHOW_E (S : SHOW_B) = struct
  open S
  let show (x:s) : string  = shows x ""
end

(* Class SHOW Extended with defaults and other operators *)
module SHOW (M : SHOW_B) = struct
  (* type "s" imported from M but abstract! *)
  include M
  include SHOW_E(M)
  (* let show (x:s) : string  = shows x "" *)
end

(* module SHOW_E (S : SHOW_B) = struct *)
(*   (\* type "s" imported from M *\) *)
(*   let show (x:S.s) : string  = S.shows x "" *)
(* end *)




