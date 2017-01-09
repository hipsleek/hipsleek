relation Uf(int n, int r).


int fact(int x)
  infer [Uf]
  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
