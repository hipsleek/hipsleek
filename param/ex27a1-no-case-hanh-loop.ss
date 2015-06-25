
relation R(int x,int y).

void loo (int x, int y)
 infer [R]
  requires R(x,y)
     ensures true;
     /*case {
  x <= 0 -> requires R(x,y) & Term ensures true;
  x > 0 -> case {
   x+y < 0 -> requires R(x,y) & Term[x] ensures true;
   x+y >= 0 -> requires R(x,y) & Loop ensures false;
  }
 }
     */
{
  if (x>0) {
    x = x+x+y;
    y=y+1;
    loo(x,y);
  };
}

/*
# ex27a1.ss 

!!! **panalysis.ml#103:constraints of x':[ x'=y+(2*x)]
!!! **panalysis.ml#103:constraints of y':[ y'=y+1]
!!! **panalysis.ml#13:specvar: :x'
!!! **panalysis.ml#33:lhs terms: :( 1)*x'^1
!!! **panalysis.ml#35:rhs terms: :( 1)*y^1 + ( 2)*x^1
!!! **panalysis.ml#43:rearranged: : 1*x'=(1*y)+(2*x)
!!! **panalysis.ml#13:specvar: :y'
!!! **panalysis.ml#33:lhs terms: :( 1)*y'^1
!!! **panalysis.ml#35:rhs terms: :( 1)*y^1 + ( 1)
!!! **panalysis.ml#43:rearranged: : 1*y'=(1*y)+1


 */
