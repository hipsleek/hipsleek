// This example seems hard to handle by our
// current termination logic system.

ranking r1(int x,int y).
ranking r2(int x,int y).
ranking r3(int x,int y).
relation b1(int x, int y, int z).
relation b2(int x, int y, int z).
relation b3(int x, int y, int z).
relation ans(int x, int y, int z).
relation ans2(int x, int y, int z).

int swap (int x, int y)
  infer @pre [r1,r2,r3,ans,ans2,b1,b2,b3]
 case {
  x=0 -> requires Term[] ensures b1(x,y,z);
  x<0 -> 
   case {
    y<0 -> requires Loop[] ensures false;
    y=0 -> requires Term[] ensures b2(x,y,z);
    y>0 -> requires Term[r1(x,y) /*2*y+1*/] ensures ans2(x,y,res); 
    }
   x>0 ->
     case {
     y<0 -> requires Term[r2(x,y) /* 2*x */] ensures ans2(x,y,res); 
     y=0 -> requires Term[] ensures b3(x,y,z);
     y>0 -> requires Term[r3(x,y) /* x+y */] ensures ans(x,y,res);
  }
 }
{
   if (x!=0) 
     return swap(y,x-1);
	else 
      return y;
}

/*
FIXPOINT computation may be delayed?

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
1. (r1(x,y))>(r2(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] WITH r2[1]<0,r2[2]>=1
2. (r2(x,y))>(r1(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] WITH r2[1]>=2,r2[2]<0
3. (r3(x,y))>(r3(y',v))]  
       [r3[1]->r3[2]:DEC(1); r3[2]->r3[1]:NC] WITH r2[1]>=2,r2[2]>=1

USE LP to solve for a,b,c,z1-3.

 r1(x,y) = ay+z1
 r2(x,y) = ay+z2
 r3(x,y) = bx+cx+z3


!!! NEW RELS:[ 
( v_int_29_482'=res & v_int_29_713=x - 1 & x<=(0 - 1) & 1<=y & 
ans2(y,v_int_29_713,v_int_29_482')) -->  ans2(x,y,res), 
( x=1 & y<=(0 - 1)) -->  ans2(x,y,res), ( v_int_29_482'=res & v_int_29_739=x - 1 & y<=(0 - 1) & 2<=x & 
ans2(y,v_int_29_739,v_int_29_482')) -->  ans2(x,y,res), 

( x=1 & 1<=y) -->  ans(x,y,res), 
( v_int_29_482'=res & v_int_29_784=x - 1 & 2<=x & 1<=y & 
ans(y,v_int_29_784,v_int_29_482')) -->  ans(x,y,res)]

*/
