
relation P(int n).
relation Q(int n,int r).


int id(int n)
  infer [P,Q]
  requires P(n) ensures Q(n,res);
{
  if (n==0) return 0;
  else return 1+id(n-1);
}
