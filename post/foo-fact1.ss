
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
  infer [
         @term,
         @post_n
 ]
  requires true ensures true;
//  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return foo(1) + fact(x - 1);
}
/*
# foo-fact1.ss

Please strengthen spec with an unknown post, e.g.
  requires true  ensures Upost1(x,res);
Before inference.

*/
