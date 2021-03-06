// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
// 90 -> 91
int f91(int n)
  infer [@term]
  requires true
  ensures ((res=91 & n<=90) | (n=res & 91<=res));
/*
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }
*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
