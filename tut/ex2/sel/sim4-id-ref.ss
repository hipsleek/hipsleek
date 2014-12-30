
relation P(int n).
  relation Q(int n,int m,int r).


int id(ref int n)
  infer [P,Q]
  requires P(n) ensures Q(n,n',res);
{
  if (n==0) return 0;
  else return 1+id(n-1);
}

