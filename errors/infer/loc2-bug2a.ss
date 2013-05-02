int foo (int n)
 requires true
  ensures res<0;
 {
   int r;
   r = 3;
   return r;
 }
