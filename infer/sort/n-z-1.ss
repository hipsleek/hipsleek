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

!!! REL POST :  true
!!! POST:  true
!!! REL PRE :  P(x,y)
!!! PRE :  true


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










