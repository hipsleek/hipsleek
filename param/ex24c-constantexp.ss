relation R(int x).

void f (ref int x)
     infer [R]
     requires R(x)
     ensures true;
{
  if (x == 10) {
    f(10);
  }
}



/*
# ex24c.ss

!!! analyse_param summary:
!!! relations (normalised):[]
!!! args:[(int,x)]
!!! result:[]
!!!
(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( v_int_9_1151'=10, R(v_int_9_1151'))]
analyse_param inp2 :[(int,x)]
analyse_param@1 EXIT:[]


 */
