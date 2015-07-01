relation R(int x).

void f (ref int x)
     infer [R]
     requires R(x)
     ensures true;
{
  if (x == 10) {
    f(x);
  }
}



/*
# ex24b.ss

!!! **panalysis.ml#164:constraints of x':[]
!!! analyse_param summary:
!!! relations (normalised):[( x'=10 & x=10 & R(x), R(x'))]
!!! args:[(int,x)]
!!! result:[[FLO(x')]]
!!!
(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( x'=10 & x=10 & R(x), R(x'))]
analyse_param inp2 :[(int,x)]
analyse_param@1 EXIT:[[FLO(x')]]

 */
