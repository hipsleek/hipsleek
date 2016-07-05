//logical int p1,p2,p3;
ranking r(int x,int y).

int swap (int x, int y)
 infer[r]
 case {
  x<=0 -> requires Term[] ensures res=y;
  x>0 ->
   case {
    y<=0 -> requires Term[] ensures true;
    y>0 -> requires Term[r(x,y)] ensures true;
      }
 }
{
	if (x>0) 
		return swap(y, x-1);
	else 
      return y;
}
/*
swap.ss

BOUNDED
-------
( 1<=y & 1<=x) -->  (r(x,y))>=0, 
RANKING
-------
( v_int_16_470'=x - 1 & y'=y & 2<=x & 1<=y) 
      -->  (r(x,y))>(r(y',v_int_16_470'))]

ANALYSIS
  r(x,y)>r(y',x)  [r(1)->r(2):DEC(1); r(2)->r(1):NC]
*/
