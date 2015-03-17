int double(int n)
  requires true
  ensures  res=2*n;
{
  int r=0;
  while (n!=0) 
    requires true
    ensures n'=0 & r'=2*n+r;
  {
    n=n-1;
    r=r+2;
  }
  return r;
}

// tail-recursive counterpart
void tail_db(ref int n, ref int r)
   requires true
   ensures n'=0 & r'=2*n+r;
{
  if (n!=0) {
    n=n-1;
    r=r+2;
    tail_db(n,r);
  }
}

