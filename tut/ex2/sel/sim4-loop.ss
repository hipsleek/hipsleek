
relation P(int n,int m).
relation Q(int n,int m,int r,int p).

/*
  while (n>=0) do
  {
     n=n-1;
     r=r+1;
  }
*/

void loop(ref int n,ref int r)
  infer [P,Q]
  requires P(n,r) ensures Q(n,n',r,r');
{
  if (n>=0) {
    n=n-1;
    r=r+1;
    loop(n,r);
  }
}
