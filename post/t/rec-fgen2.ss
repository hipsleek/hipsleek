// McCarthy generic 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
int f(int n, int k)
//if spec below used, term error occurs.
//requires true
//ensures true;
infer[@term]
case {
  n>k ->  ensures res=n;
  n<=k ->  ensures res=k;
}
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}

/*
# rec-fgen1.ss

infer[@term]
case {
  n>=k ->  ensures res=n;
  n<k ->  ensures res=k;
}

Termination Inference Result:
f:  case {
  k<=n -> requires emp & Term[29,1]
 ensures emp & res=n; 
  n<k -> requires emp & Term[29,3,-1+(-1*n)+(1*k)]
 ensures emp & res=k; 
  }


*/
