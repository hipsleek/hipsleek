// This example seems hard to handle by our
// current termination logic system.

ranking r1(int x,int y).
ranking r2(int x,int y).
ranking r3(int x,int y).

int swap (int x, int y)
 infer[r1,r2,r3]
 case {
  x=0 -> requires Term[] ensures true;
  x<0 -> 
   case {
    y<0 -> requires Loop[] ensures false;
    y=0 -> requires Term[] ensures true;
    y>0 -> requires Term[r1(x,y)] ensures true; /*2*y+1*/
    }
   x>0 ->
     case {
      y<0 -> requires Term[r2(y,x) /* 2*x */] ensures true; 
      y=0 -> requires Term[] ensures true;
      y>0 -> requires Term[r3(x,y) /* x+y */] ensures true;
  }
 }
{
   if (x!=0) 
     return swap(y,x-1);
	else 
      return y;
}

/*
BOUNDED
-------
( x<=(0 - 1) & 1<=y) -->  (r1(x,y))>=0, 
( y<=(0 - 1) & 1<=x) -->  (r2(y,x))>=0, 
( 1<=y & 1<=x) -->  (r3(x,y))>=0, 

DECREASING
----------
( v_int_27_474'=x - 1 & y'=y & x<=(0 - 1) & 1<=y) 
  -->  (r1(x,y))>(r2(v_int_27_474',y')), 
( y'=y & v_int_27_474'=x - 1 & y<=(0 - 1) & 2<=x) 
  -->  (r2(y,x))>(r1(y',v_int_27_474')), 
( v_int_27_474'=x - 1 & y'=y & 2<=x & 1<=y) 
  -->  (r3(x,y))>(r3(y',v_int_27_474'))]

*/
