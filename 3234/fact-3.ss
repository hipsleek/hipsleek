relation facta(int n, int f).
axiom n=0 ==> facta(n,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

int fact(int n)
  requires n>=0
  ensures facta(n,res);
{
  int y=1;
  int z=0;
  while (z!=n)
    requires y>0 & z>=0  & z<=n & facta(z,y) & Term[n-z]
    ensures  z'=n & y'>0 & facta(n,y'); //'
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

