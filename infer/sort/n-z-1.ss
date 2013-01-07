/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P]
  requires y>=x & x>=0 & P(x,y)
  ensures  res=x;

/*
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: 
( x=v_int_77_513'+1 & y=v_int_77_512'+1 & 0<=v_int_77_513' & 
v_int_77_513'<=v_int_77_512' & P(x,y)) -->  P(v_int_77_513',v_int_77_512')]
*************************************
*************************************
*******fixcalc of pure relation *******
*************************************
[( P(v_int_77_513',v_int_77_512'), false)]
*************************************

!!! REL :  P(v_int_77_513',v_int_77_512')
!!! POST:  false
!!! PRE :  false

PROBLEM:

Precondition should not be subjected to a bottom-up fixpoint analysis.
Instead, we should just use an inductive test to check that
its inferred proof obligation condition is satisfied recursively. 

In our case, we inferred:
    P(a,b) -> true

Substituting this into our definition below trivially satisfy:
  ( x=v_int_77_513'+1 & y=v_int_77_512'+1 & 0<=v_int_77_513' & 
   v_int_77_513'<=v_int_77_512' & P(x,y)) 
   -->  P(v_int_77_513',v_int_77_512')]
since:
  ( x=v_int_77_513'+1 & y=v_int_77_512'+1 & 0<=v_int_77_513' & 
   v_int_77_513'<=v_int_77_512' & true) 
   --> true]

*/
{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1+zip(x-1,y-1);
  }
}










