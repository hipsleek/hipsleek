relation facta(int n, int f).
axiom n=0 ==> facta(n,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

int fact(int z, int n)
  requires n>=0 & z>n
  ensures facta(n,res);
{
  int y=1;
  while (z!=n)
    requires z>n
    ensures  false;
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

