// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
int f(int n, int k)
requires true
ensures true;
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}

int f91(int n)
 case {
  n>=91 -> ensures res=n;
  n<91 -> ensures res=91;
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
