

int double (int n)
 requires true
  ensures res=2*n;
 {
   if (n==0)
     return 0;
   else
     return 3+double(n);
 }
