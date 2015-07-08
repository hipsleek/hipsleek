
relation R(int x,int y).

  void loo (int x,int y)
  infer [R]  requires R(x,y) ensures true;
{
  int t;
  if (x > 0) {
    assume t' < 0;
    x = x + y + t;
    y = y - 1;
    loo(x,y);
  };
}

/*
# ex31b.ss

!!! **panalysis.ml#153:constraints of x':[ x'<=(y'+x)]
!!! **panalysis.ml#153:constraints of y':[ y=y'+1]
!!! **panalysis.ml#13:specvar: :x'
!!! **panalysis.ml#37:lhs terms: :( 1)*x'^1
!!! **panalysis.ml#39:rhs terms: :( 1)*y'^1 + ( 1)*x^1
!!! **panalysis.ml#47:rearranged: : 1*x'=(1*y')+(1*x)
!!! **panalysis.ml#13:specvar: :y'
!!! **panalysis.ml#37:lhs terms: :( 1)*y^1
!!! **panalysis.ml#39:rhs terms: :( 1)*y'^1 + ( 1)
!!! **panalysis.ml#47:rearranged: : -1*y'=1+(-1*y)
!!! analyse_param summary:
!!! relations (normalised):[( y=y'+1 & 1<=x & x'<=(y'+x) & R(x,y), R(x',y'))]
!!! args:[(int,x),(int,y)]
!!! result:[[DECEQ([y',x], (1*y')+(1*x)),IND([y], -1+(1*y))]]
!!!
(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( y=y'+1 & 1<=x & x'<=(y'+x) & R(x,y), R(x',y'))]
analyse_param inp2 :[(int,x),(int,y)]
analyse_param@1 EXIT:[[DECEQ([y',x], (1*y')+(1*x)),IND([y], -1+(1*y))]]

 */
