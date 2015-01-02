relation Q(int n,int r).

int foo(int n)
  infer [Q]
  requires true  ensures Q(n,res);
{
  return 1+n;
}

