open Random

let get_random f t =
  if f>t
  then failwith ("get_random: Invalid input "^(string_of_int f)^" "^(string_of_int t))  else f+(int (t-f+1))
;;

let yes_or_no () =
  get_random 0 2 = 0
;;
