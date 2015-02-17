type frac = int * int

type valfrac = bool * (int * int)

let string_of_frac (num, den) =
  (string_of_int num) ^ "/" ^ (string_of_int den)

let eq_frac (n1, d1) (n2, d2) =
  (n1 * d2) == (n2 * d1)

let less_eq_frac (n1,d1) (n2,d2) =
  (n1 * d2) <= (n2 *d1)

(* need to normalize *)
let substract (n1,d1) (n2,d2) =
  ((n1*d2 - n2*d1),(d1*d2))

let isFull (n,d) == n=d

let isZero (n,d) == n=0

let mkFrac ?(value=true) n d = (value,(n,d))

let full2frac  = mkFrac ~value:false 1 1

let value2frac = mkFrac 1 1

(* we need a flag to indicate if a frac is orig @full or @value *)


