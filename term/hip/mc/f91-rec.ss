// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
int f(int n, int k)
//if spec below used, term error occurs.
//requires true
//ensures true;
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=k -> requires Term[] ensures res=n;
  n<k -> requires Term[k-n] ensures res=k;
}
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}

// 90 -> 91
int f91(int n)
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
