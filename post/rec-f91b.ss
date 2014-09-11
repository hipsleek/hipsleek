
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
infer [postA]
requires true
  ensures postA(n,res);
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

int fact(int n)
infer [postB]
  requires true ensures postB(n,res);
{
  if (n==0) return 0;
  else return 1+fact(0);
}
