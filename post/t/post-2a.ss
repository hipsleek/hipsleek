
relation Uf(int n, int r).

int fact(int x)
  infer [Uf]
  requires x>=0 ensures Uf(x,res);
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
  requires x>=0
  ensures res=1+2*x & x>=0;
*/
