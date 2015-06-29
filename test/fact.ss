//relation ff(int n, int r).

int aux(int n)
//infer [ff]
 requires n>=0
  ensures res>=0;
//ff(n,res);
{
  if (n==0) return 0;
  else return n + aux(n-1);
}
