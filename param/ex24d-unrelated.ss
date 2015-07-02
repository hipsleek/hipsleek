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

!!! analyse_param summary:
!!! relations (normalised):[]
!!! args:[(int,x),(int,y),(int,z)]
!!! result:[]
!!!
(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( x=x'+1 & z'=y'+x' & 0<=x' & R(x,y,y'), R(x',y',z'))]
analyse_param inp2 :[(int,x),(int,y),(int,z)]
analyse_param@1 EXIT:[]

Relations 'filtered out' as insignificant. Hrmm.
z'=x'+y' is (atm) considered "not useful" since it doesn't have
both some unprimed and primed specvars. (eg z=f(z')).

 */
