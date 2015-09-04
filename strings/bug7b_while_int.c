int test(int n)
  /*@
     requires true
     ensures res=0;
  */
 {
     while (n!=0) 
       /*@ 
          case {
            n>=0 -> ensures n'=0;
            n<0 -> ensures false;
          }
       */
     {   
         n--;
     }
     return 0;
 }

/*=================================
#bug7b.c
Checking procedure while_7_5$int... 
!!! **typechecker.ml#946:
 Before CheckPost : 2
!!! **typechecker.ml#949:
 After CheckPost : 1
[UNSOUNDNESS] WARNING : possible new unsatisfiable state from post-proving of bug7b_while_int.c_12:27_12:31

Post condition cannot be derived:
  (may) cause: OrL[
 (n'+1+1)!=0 & (n'+1)!=0 & n!=0 & n'+1+1=n |-  1+n'=n. LOCS:[15;7;14] (must-bug),
valid
]
*/
