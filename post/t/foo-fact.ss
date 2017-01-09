
relation Uf(int n, int r).
  relation Uf1(int n, int r).

  int foo(int n)
 case {
  n>0 -> ensures res=n+1;
  n<=0 -> ensures res=n-1;
 }
/*
  infer [Uf1]
  requires true
  ensures Uf1(n,res);
*/
{
  if(n>0)
  return n+1;
  else return n-1;
}

int fact(int x)
  infer [Uf]
  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return foo(1) + fact(x - 1);
}
/*
# foo-fact.ss

This currently prints:

!!!REL POST :  Uf(x,res)
!!!POST:  res=1+(2*x) & 0<=x

Can we merge this post into our spec,
and then print it; as follows:

Post Inference result:
fact:
  requires true 
  ensures res=1+2*x & x>=0;

The print out from @term is as follows:

Termination Inference Result:
fact:  case {
  1<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=(0-1) -> requires emp & MayLoop[]
 ensures emp & true; 
  x=0 -> requires emp & Term[31,1]
 ensures emp & true; 
  }

*/
