open VarGen

#include "xdebug.cppo"

 let foo x = x+1

 let foo x =
   let pr = string_of_int in
   Debug.ho_1 "foo" pr pr foo x 

 let () = x_binfo_hp Gen.pr_id "hello" no_pos;;

 let () = x_binfo_hp Gen.pr_id "hello2" no_pos;;

 let () = x_binfo_hp Gen.pr_id "hello" no_pos;;

 let x = x_add foo 2 ;;

 let x = foo 3 ;;

 let x = x_add foo 4 ;;

 let x = x_add foo 5 ;;

 (* let x = foo 6 ;; *)

 let x = foo 7 ;;


