// McCarthy generic 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
int f(int n, int k)
//if spec below used, term error occurs.
infer[@term]
requires true ensures true;
/*
case {
  n>k ->  ensures res=n;
  n<=k ->  ensures res=k;
}
*/
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}

/*
# rec-fgen3.ss

MayLoop cases can be combined if their post are identical

Termination Inference Result:
f:  case {
  n<k & n<=(k-2) & n<=(k-3) & n<=(k-4) & n<=(k-5) & n<=(k-
  6) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<k & n<=(k-2) & n<=(k-3) & n<=(k-4) & n<=(k-5) & k<=(n+
  5) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<k & n<=(k-2) & n<=(k-3) & n<=(k-4) & k<=(n+
  4) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<k & n<=(k-2) & n<=(k-3) & k<=(n+
  3) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<k & n<=(k-2) & k<=(n+2) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<k & k<=(n+1) -> requires emp & MayLoop[]
 ensures emp & true; 
  k<=n -> requires emp & Term[29,1]
 ensures emp & true; 
  }


*/
