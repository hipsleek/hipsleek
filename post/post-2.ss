
relation Uf(int n, int r).

int fact(int x)
  infer [Uf]
  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# post-2.ss

This currently prints:

!!!REL POST :  Uf(x,res)
!!!POST:  x=res-1 & 1<=res
!!!REL PRE :  true

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
