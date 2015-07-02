relation R(int x, int y, int z).

void f (ref int x, ref int y, int z)
     infer [R]
     requires R(x,y,z)
     ensures true;
{
  if (x > 0) {
    x = x - 1;
    y = z;
    z = x + y;
    f(x,y,z);
  }
}



/*
# ex24d.ss

!!! **panalysis.ml#159:constraints of x':[ x=x'+1]
!!! **panalysis.ml#159:constraints of y':[]
!!! **panalysis.ml#159:constraints of z':[]
!!! **panalysis.ml#13:specvar: :x'
!!! **panalysis.ml#37:lhs terms: :( 1)*x^1
!!! **panalysis.ml#39:rhs terms: :( 1)*x'^1 + ( 1)
!!! **panalysis.ml#47:rearranged: : -1*x'=1+(-1*x)
!!! analyse_param summary:
!!! relations (normalised):[( x=x'+1 & z'=y'+x' & 0<=x' & y'=z & R(x,y,z), R(x',y',z'))]
!!! args:[(int,x),(int,y),(int,z)]
!!! result:[[IND([x], -1+(1*x)),UNK(y'),UNK(z')]]
!!!
(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( x=x'+1 & z'=y'+x' & 0<=x' & R(x,y,y'), R(x',y',z'))]
analyse_param inp2 :[(int,x),(int,y),(int,z)]
analyse_param@1 EXIT:[[IND([x], -1+(1*x)),UNK(y'),UNK(z')]]

 */
