
relation R(int x).

  void loo (int x)
  infer [R]  requires R(x) ensures true;
{
  int t;
  if (x > 0) {
    assume t' > 0;
    x = x + t;
    loo(x);
  };
}

/*
# ex31d.ss

!!! analyse_param summary:
!!! relations (normalised):[( 1<=x & x<x' & R(x), R(x'))]
!!! args:[(int,x)]
!!! result:[[DEC([x], 1*x)]]

output *should be* INC.

 */
