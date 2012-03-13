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
    y>0 -> requires Term[r1(x,y) /*2*y+1*/] ensures true; 
    }
   x>0 ->
     case {
      y<0 -> requires Term[r2(x,y) /* 2*x */] ensures true; 
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
( y<=(0 - 1) & 1<=x) -->  (r2(x,y))>=0, 
( 1<=y & 1<=x) -->  (r3(x,y))>=0, 

DECREASING
----------
( v=x - 1 & y'=y & x<=(0 - 1) & 1<=y) 
  -->  (r1(x,y))>(r2(y',v)), 
( y'=y & v=x - 1 & y<=(0 - 1) & 2<=x) 
  -->  (r2(x,y))>(r1(y',v)), 
( v=x - 1 & y'=y & 2<=x & 1<=y) 
  -->  (r3(x,y))>(r3(y',v))]

ANALYSIS
========
( x<=(0 - 1) & 1<=y) -->  (r1(x,y))>=0, 
   => r1[1]<=-1 & r1[2]>=1
( y<=(0 - 1) & 1<=x) -->  (r2(x,y))>=0,
   => r2[1]>=1 & r2[2]<=-1
( 1<=y & 1<=x) -->  (r3(x,y))>=0, 
   => r3[1]>=1 & r3[2]>=1

1. (r1(x,y))>(r2(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] 
2. (r2(x,y))>(r1(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] 
3. (r3(x,y))>(r3(y',v))]  
       [r3[1]->r3[2]:DEC(1); r3[2]->r3[1]:NC] 

USE LP to solve for a,b,c,z1-3.

 r1(x,y) = ay+z1
 r2(x,y) = ay+z2
 r3(x,y) = bx+cx+z3

*/
