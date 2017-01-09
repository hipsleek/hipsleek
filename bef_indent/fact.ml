#include "xdebug.cppo"
let rec fact n = 
  if (n==0) then 1
  else n * (fact (n-1)) ;;

print_endline (string_of_int (fact 10));;
