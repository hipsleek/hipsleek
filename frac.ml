(* type frac = int * int *)

type frac = bool option * (int * int)

let string_of_frac (num, den) =
  (string_of_int num) ^ "/" ^ (string_of_int den)

let eq_frac (n1, d1) (n2, d2) =
  (n1 * d2) == (n2 * d1)

let less_eq_frac (n1,d1) (n2,d2) =
  (n1 * d2) <= (n2 *d1)

(* need to normalize *)
let subtract (n1,d1) (n2,d2) =
  ((n1*d2 - n2*d1),(d1*d2))

let eq_frac (_,r1) (_,r2) =
  eq_frac r1 r2

let less_eq_frac (_,r1) (_,r2) =
  less_eq_frac r1 r2

let subtract (d,r1) (_,r2) =
  (d,subtract r1 r2)

let string_of_frac (d,r) =
  let s = match d with 
      None -> ""
    | Some f -> if f then "V" else "F" 
  in s^(string_of_frac r)

let isFull (n,d) = n=d

let isZero (n,d) = n=0

let make ?(value=None) n d : frac = 
  if d<=0 then failwith "frac cannot have zero or -ve denominator"
  else if n<0 then failwith "frac cannot have -ve numerator"
  else (value,(n,d))

let full2frac  = make ~value:(Some false) 1 1

let value2frac = make ~value:(Some true) 1 1

(* we need a flag to indicate if a frac is orig @full or @value *)


