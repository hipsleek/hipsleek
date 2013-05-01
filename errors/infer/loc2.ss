

int double (int n)
 requires true
  ensures res=2*n;
 {
   if (n==0)
     return 0;
   else
     {
       int k;
       k = 3;
     return k+double(n-1);
     }
 }
