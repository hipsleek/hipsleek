

int double (int n)
 requires true
  ensures res=2*n;
 {
   if (n==0)
     return 0;
   else
     {
       int k,r;
       k = 3;
       r = k+double(n-1);
       return r;
     }
 }

/*
Checking procedure double$int... 
Post condition cannot be derived:
  (must) cause:  res=v_int_13_771+v_int_13_771+3 & (v_int_13_771+1)!=0 & n=v_int_13_771+1 |-
  res=n+n. LOCS:[13;7;3;5] (must-bug)

  WHY isn't line 12 included?
 */

int foo (int n)
 requires true
  ensures res>0;
 {
   int r;
   r = -3;
   return r;
 }
