relation Uf(int n, int r).
  relation Uf1(int n, int r).

  int foo(int n)
  infer [Uf1]
  requires true
  ensures Uf1(n,res);
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
