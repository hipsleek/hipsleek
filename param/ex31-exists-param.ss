
relation R(int x).

void loo (ref int x)
     infer [R]  requires R(x) ensures true;
{
  int t;
  if (x>0) {
    assume t'<0;
    x = x+t;
    loo(x);
  };
}

/*
# ex31.ss

void loo (ref int x)
     infer [R]  requires R(x) ensures true;
{
  int t;
  if (x>0) {
    assume t'<0;
    x = x+t;
    loo(x);
  };

!!! **panalysis.ml#118:constraints of x':[]
!!! analyse_param summary:
!!! relations:[( x'<x & 1<=x & R(x), R(x'))]
!!! args:[(int,x)]
!!! result:[[FLO(x')]]
!!! 

(==cformula.ml#1725==)
analyse_param@1
analyse_param inp1 :[( x'<x & 1<=x & R(x), R(x'))]
analyse_param inp2 :[(int,x)]
analyse_param@1 EXIT:[[FLO(x')]]

# This is definitely not FLO but it could be
  classified as decreasing due to x'<x, and you may use DEC(x) 
  which denotes a value < x at the next call.

 */
