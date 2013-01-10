/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b) == x<=y.

void error()
  requires false
  ensures true;

int zip(int x, int y)
  infer [R]
  requires x>=0 & y>=0 & P(x,y)
  ensures  R(res,x,y);

/*
*************************************
*******fixcalc of pure relation *******
*************************************
[( R(res,x,y), res=x & 0<=x & x<=y, true, true)]
*************************************

!!! REL POST :  R(res,x,y)
!!! POST:  res=x & 0<=x & x<=y
!!! REL PRE :  true
!!! PRE :  true
Procedure zip$int~int SUCCESS


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










