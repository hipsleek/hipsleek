relation R(int x,int a).
relation R2(int x).

void loo (ref int x, int a)
  infer [R,R2]
     requires R(x,a)
     ensures true;
{

  if (x>0) {
    a=a+1;
    x = x+a-1;
    loo2(x);
  };
}

void loo2 (ref int xx)
  infer [R,R2]
     requires R2(xx)
     ensures true;
{

  if (xx>0 ) {
    loo(xx,5);
  };
}

/*
# ex26d.ss

R2(xx) --> R(...)
!!! **infer.ml#2213:RelInferred (simplified):[
RELDEFN R: ( v_int_24_1327'=5 & 1<=xx' & R2(xx')) -->  R(xx',v_int_24_1327')]

!!! analyse_param summary:
!!! relations (normalised):[( v_int_24_1327'=5 & 1<=xx' & xx'=xx & R2(xx), R(xx',v_int_24_1327'))]
!!! args:[(int,xx)]
!!! result:[[FLOW(xx),CONST( 5)]]

R(..) --> R2(xx)
!!! **infer.ml#2213:RelInferred (simplified):
 [RELDEFN R2: ( x=x'-a & a<x' & R(x,a)) -->  R2(x')]

!!! analyse_param summary:
!!! relations (normalised):[( x=x'-a & a<x' & R(x,a), R2(x'))]
!!! args:[(int,x),(int,a)]
!!! result:[[IND([a,x], (1*a)+(1*x))]]

 */
