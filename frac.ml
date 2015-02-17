type frac = int * int

let string_of_frac (num, den) =
  (string_of_int num) ^ "/" ^ (string_of_int den)

let eq_frac (n1, d1) (n2, d2) =
  (n1 * d2) == (n2 * d1)

let less_eq_frac (n1,d1) (n2,d2) =
  (n1 * d2) <= (n2 *d1)

let substract (n1,d1) (n2,d2) =
  ((n1*d2 - n2*d1),(d1*d2))
