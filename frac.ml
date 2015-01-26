type frac = int * int

let string_of_frac (num, den) =
  (string_of_int num) ^ "/" ^ (string_of_int den)