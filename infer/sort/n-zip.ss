/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [P,R]
  requires P(x,y)
  ensures  R(res,x,y);
/*

  infer [x,y,R]
  requires x>=0 & y>=0
  ensures  R(res,x,y);

!!! REL :  R(res,x,y)
!!! POST:  x>=0 & y>=x & res=x
!!! PRE :  0<=x & x<=y
P
  infer [R,P]
  requires P(x,y)
  ensures  R(res,x);
Checking procedure zip$int~int... 
( [(138::,0 ); (138::,0 ); (137::,1 ); (137::,1 )]) :n-zip.ss:36: 7: Proving precondition in method failed
*/
/*
  infer [R]
  requires 0<=x<=y
  ensures  R(res,x);
*************************************
[RELDEFN R: ( x=0 & res=0) -->  R(res,x),
RELDEFN R: ( v_int_26_577=res-1 & v_int_26_573=x-1 & 1<=x & R(v_int_26_577,v_int_26_573)) -->  R(res,x)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( R(res,x), x>=0 & res=x)]
*/
/*
  requires 0<=x<=y
  ensures  res=x;
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










