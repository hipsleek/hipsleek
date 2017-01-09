
relation P(int n,int m).
relation Q(int n,int m,int r).

void is_zero(int m)
  requires m=0
  ensures true;

void is_pos(int m)
  requires m>0 ensures true;


int zip(int n,int m)
  infer [P,Q]
  requires P(n,m) ensures Q(n,m,res);
{
  if (n==0) {
      is_zero(m);
      return 0;
  }
  else {
       is_pos(m);
       is_pos(n);
       return 1+zip(n-1,m-1);
  }
}

