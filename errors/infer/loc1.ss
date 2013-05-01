int double (int n)
 requires true
  ensures res=2*n;
 {
   if (n==0)
     return 1;
   else
     return 2+double(n-1);
 }
