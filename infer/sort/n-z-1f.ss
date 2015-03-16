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

!!! REL POST :  R(res,x,y)
!!! POST:  res=x & 0<=x
!!! REL PRE :  P(x,y)
!!! PRE :  (y<=(0-1) & 0<=x) | (0<=x & x<=y)
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










