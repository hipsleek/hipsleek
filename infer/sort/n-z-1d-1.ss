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
!!! REL POST :  R(res,x,y)
!!! POST:  res=x & 0<=x & x<=y
!!! REL PRE :  P(x,y)
!!! PRE :  0<=x & x<=y
Procedure zip$int~int SUCCESS

PROBLEM : since P is not in the selected var list [R], we should
not really have infer pre-conditionfor it, esp when there is
a definition is given for it.

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










