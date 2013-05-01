
relation R(int a,int b,int c).
int max2(int a,int b)
 requires true
 ensures res=max(a,b);

int fib(int n,int m)
 infer [R]
 requires n>=0 & m>=0
 //ensures  res=m+max(1,n);
 ensures  R(res,m,n);
  { int r;
   m = m+1;
   if (n<=1) r=0;
   else r=max2(fib(n-1,m),fib(n-2,m));
   return max2(m,r);
 }  

/*

PROBLEM : fixcalc seems imprecise below.

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(res,m,n), m>=0 & res>=(1+m) & n>=0 & res>=(m+n))]
*************************************

Better to have:
[( R(res,m,n), m>=0 & res>=(1+m) & n>=0 & res>=(m+n))
         & (res<=1+m || res<=m+n)

!!! POST:  (m>=0 & res>=(2+m) & res=n+m) | (n>=0 & 1>=n & m>=0 & res=m+1)

*/
