
relation R(int x,int y).

  void loo (int x,int y)
  infer [R]  requires R(x,y) ensures true;
{
  int t;
  int s;
  if (x > 0) {
    assume t' < 0;
    assume s' > 0;
    y = y + s;
    x = x + y + t;
    loo(x,y);
  };
}

/*
# ex31c.ss

!!! analyse_param summary:
!!! relations (normalised):[( y<y' & 1<=x & x'<(x+y') & R(x,y), R(x',y'))]
!!! args:[(int,x),(int,y)]
!!! result:[[DEC([x,y'], (1*x)+(1*y')),INC([y], 1*y)]]

need to remove the primed vars.. but, cannot since y'>y,
so UNK.

 */
