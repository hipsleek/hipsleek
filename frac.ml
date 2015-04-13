#include "xdebug.cppo"
(* type frac = int * int *)

(* type frac = bool option * (int * int) *)
type frac = bool option * Ratio.ratio

(* let string_of_frac (num, den) = *)
(*   (string_of_int num) ^ "/" ^ (string_of_int den) *)


(* let eq_frac (n1, d1) (n2, d2) = *)
(*   (n1 * d2) == (n2 * d1) *)

(* let less_eq_frac (n1,d1) (n2,d2) = *)
(*   (n1 * d2) <= (n2 *d1) *)


(* need to normalize *)
(* let subtract (n1,d1) (n2,d2) = *)
(*   ((n1*d2 - n2*d1),(d1*d2)) *)
let subtract = Ratio.sub_ratio
;;


let eq_frac (_,r1) (_,r2) =
  Ratio.eq_ratio r1 r2

let less_eq_frac (_,r1) (_,r2) =
  Ratio.le_ratio r1 r2


(* Take the value from only one of them? What if they are different? *)
let subtract (d,r1) (_,r2) =
  (d, Ratio.sub_ratio r1 r2)

let comb d1 d2 = 
  match d1,d2 with
  | None, x -> x
  | x, None -> x
  | Some f1, Some f2 ->Some (f1 && f2)

let add (d1,r1) (d2,r2) =
  (comb d1 d2, Ratio.add_ratio r1 r2)

let is_false (_,r1) = 
  let n = Ratio.numerator_ratio r1 in 
  let d = Ratio.denominator_ratio r1 in 
  Big_int.gt_big_int n d

let is_unit (_,r1) = 
  let n = Ratio.numerator_ratio r1 in 
  let d = Ratio.denominator_ratio r1 in 
  Big_int.eq_big_int n d

let is_zero (_,r1) = 
  let n = Ratio.numerator_ratio r1 in 
  Big_int.sign_big_int n = 0

let is_value (d,r1) = 
  match d with
  | None -> true
  | Some f -> f

let string_of_frac (d,r) =
  let s = match d with 
      None -> ""
    | Some f -> if f then "V" else "F" 
  in s^(Ratio.string_of_ratio r)

(* let isFull (n,d) = n=d *)

(* let isZero (n,d) = n=0 *)

let make ?(value=None) n d : frac = 
  if d<=0 then failwith "frac cannot have zero or -ve denominator"
  else if n<0 then failwith "frac cannot have -ve numerator"
  else (value,Ratio.create_ratio (Big_int.big_int_of_int n) (Big_int.big_int_of_int d))

let full2frac  = make ~value:(Some false) 1 1

let value2frac = make ~value:(Some true) 1 1

(* we need a flag to indicate if a frac is orig @full or @value *)


