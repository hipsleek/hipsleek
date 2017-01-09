
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
infer [postA]
requires n>=91
  ensures postA(n,res);
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
