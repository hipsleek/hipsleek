int test(int n)
  /*@
     requires true
     ensures res=0;
  */
 {
     while (n!=0) 
       /*@ 
         requires true
         ensures n = 0 & n'=0
              or n != 0 & n' = n-1;
       */
     {   
         n--;
     }
     return 0;
 }

/*=================================
#bug7b.c
Checking procedure while_7_5$int... 
Post condition cannot be derived:
  (may) cause: OrL[
UnionR[ n!=0 & n'+1+1=n & (n'+1)!=0 |-  n=0. LOCS:[14;7;12] (must-bug), n!=0 & n'+1+1=n & (n'+1)!=0 |-  1+n'=n. LOCS:[7;14] (must-bug)],
valid
]

*/
