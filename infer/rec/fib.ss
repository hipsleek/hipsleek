
relation R(int a,int b,int c).
int max2(int a,int b)
 requires true
 ensures res=max(a,b);

int fib(int n,int m)
 infer [R]
 requires n>=0 & m>=0
 ensures  R(res,m,n);
 { int r;
   m = m+1;
   if (n<=1) r=0;
   else r=fib(n-1,m);//+fib(n-2);
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

*/
