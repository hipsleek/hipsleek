relation ff(int n, int r).

int aux(int n)
 infer [ff]
 requires n>=0
  ensures //res>=1;
   ff(n,res);
{
  if (n==0) return 0;
  else return n * aux(n-1);
}

/*
# ex3.ss

# I guess multiplication has been stripped off by Omega. I wonder
if we can put it back into the inference result.

WARNING: _0:0_0:0:[omega.ml] Non-linear arithmetic is not supported by Omega.

!!! **infer.ml#2149:RelInferred (simplified):[
RELDEFN ff: ( ff(v_int_10_1198,v_int_10_1200) & res=0 
  & v_int_10_1198=n-1 & 1<=n) -->  ff(n,res)]
WARNING: _0:0_0:0:[omega.ml] Non-linear arithmetic is not supported by Omega.

*/
