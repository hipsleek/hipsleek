
relation R(int x,int y).

  void loo (int x,int y)
  infer [R]  requires R(x,y) ensures true;
{
  int t;
  int t2;
  int p;
  if (x>0) {
    assume t'<0;
    assume t2'<0;
    p =y;
    y = x+t;
    x = p+t2;
    loo(x,y);
  };
}

/*
# ex32.ss

  if (x>0) {
    assume t'<0;
    assume t2'<0;
    p =y;
    y = x+t;
    x = p+t2;
    loo(x,y);
  };

!!! **panalysis.ml#118:constraints of x':[]
!!! **panalysis.ml#118:constraints of y':[]
!!! analyse_param summary:
!!! relations:[( y'<x & x'<y & 1<=x & R(x,y), R(x',y'))]
!!! args:[(int,x),(int,y)]
!!! result:[[FLO(x'),FLO(y')]]
!!! dump:(2)**typechecker.ml#4359:

# Expects:
    !!! result:[[DEC(y),FLO(x)]]

 */
