// McCarthy 91
// 90 -> 91
relation P(int n, int r).
int f91(int n)
 infer [P]
 requires true
 ensures P(n,res);
  //  n>91 -> requires Term[] ensures res=n;
/*
 case {
  n>=91 -> ensures res=n;
  n<91 -> ensures res=91;
 }
*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
