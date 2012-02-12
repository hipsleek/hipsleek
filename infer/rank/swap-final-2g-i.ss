// This example seems hard to handle by our
// current termination logic system.

ranking r1(int x,int y).
ranking r2(int x,int y).
ranking r3(int x,int y).
relation b1(int x, int y, int z).
relation b2(int x, int y, int z).
relation b3(int x, int y, int z).
relation ans1(int x, int y, int z).
relation ans2(int x, int y, int z).
relation ans3(int x, int y, int z).

int swap (int x, int y)
  infer @pre [r1,r2,r3,ans1,ans2,ans3,b1,b2,b3]
 case {
  x=0 -> requires Term[] ensures res=y;//b1(x,y,res); /* res=y */
  x<0 -> 
   case {
    y<0 -> requires Loop[] ensures false;
    y=0 -> requires Term[] ensures res=y;//b2(x,y,res) ; /* res=y */
    y>0 -> requires Term[r1(x,y) /*2*y+1*/] ensures res=x-(y+1);// & y=1;//ans1(x,y,res); /* res=x-(y+1) */
    }
   x>0 ->
     case {
     y<0 -> requires Term[r2(x,y) /* 2*x */] ensures res=y-x;// & x=1; //ans2(x,y,res); /* res=y-x */
     y=0 -> requires Term[] ensures res=x-1;//b3(x,y,res); /* res=x-1 */
     y>0 -> requires Term[r3(x,y) /* x+y */] ensures ans3(x,y,res); /* x+y */
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
( x<=(0 - 1) & 1<=y) -->  (r1(x,y))>=0, 
( y<=(0 - 1) & 1<=x) -->  (r2(x,y))>=0, 
( 1<=y & 1<=x) -->  (r3(x,y))>=0, 

 ==> r1[1]<=-1; r1[2]>=1
 ==> r2[1]>=1; r2[1]<=-1
 ==> r3[1]>=1; r3[2]>=1


1. (r1(x,y))>(r2(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] WITH r2[1]<0,r2[2]>=1  ===> r1(x,y)=ay+z1
2. (r2(x,y))>(r1(y',v))
       [r2[1]->r1[2]:DEC(1); r2[2]->r1[1]:NC] WITH r2[1]>=2,r2[2]<0  ===> r2(x,y)=ax+z2
3. (r3(x,y))>(r3(y',v))]  
       [r3[1]->r3[2]:DEC(1); r3[2]->r3[1]:NC] WITH r2[1]>=2,r2[2]>=1

USE LP to solve for a,b,c,z1-3.

 r1(x,y) = ay+z1
 r2(x,y) = ay+z2
 r3(x,y) = bx+cy+z3

a=1; b=1; c=1; z1=1; z2=0; z3=?

( x=0 & res=y) -->  b1(x,y,res),
( y=0 & v_int_33_493'=res & x=v_int_33_700+1 & v_int_33_700<=(0 - 2) & 
  b1(y,v_int_33_700,v_int_33_493')) -->  b2(x,y,res),
( y=0 & v_int_33_493'=res & x=v_int_33_772+1 & 0<=v_int_33_772 & 
     b1(y,v_int_33_772,v_int_33_493')) -->  b3(x,y,res),

( x=1 & v_int_33_493'=res & y<=(0 - 1) & b2(y,0,v_int_33_493')) -->  ans2(x,y,res),
( v_int_33_493'=res & v_int_33_723=x - 1 & x<=(0 - 1) & 1<=y & 
   ans2(y,v_int_33_723,v_int_33_493')) -->  ans1(x,y,res),
( v_int_33_493'=res & v_int_33_749=x - 1 & y<=(0 - 1) & 2<=x & 
     ans1(y,v_int_33_749,v_int_33_493')) -->  ans2(x,y,res),

( x=1 & v_int_33_493'=res & 1<=y & b3(y,0,v_int_33_493')) -->  ans3(x,y,res),
( v_int_33_493'=res & v_int_33_798=x - 1 & 2<=x & 1<=y & 
     ans3(y,v_int_33_798,v_int_33_493')) -->  ans3(x,y,res)]


!!! NEW RELS:[ 

BASE CASES
----------
( x=0 & res=y) -->  b1(x,y,res), 
( y=0 & v_int_32_490'=res & x=v_int_32_697+1 & v_int_32_697<=(0 - 2) & 
  b1(y,v_int_32_697,v_int_32_490')) -->  b2(x,y,res)
( y=0 & v_int_32_490'=res & x=v_int_32_769+1 & 0<=v_int_32_769 & 
  b1(y,v_int_32_769,v_int_32_490')) -->  b3(x,y,res) 

REC CASES
---------
( x=1 & v_int_33_493'=res & y<=(0 - 1) & b2(y,0,v_int_33_493')) -->  ans2(x,y,res),
( v_int_33_493'=res & v_int_33_723=x - 1 & x<=(0 - 1) & 1<=y & 
     ans2(y,v_int_33_723,v_int_33_493')) -->  ans1(x,y,res),
( v_int_33_493'=res & v_int_33_749=x - 1 & y<=(0 - 1) & 2<=x & 
     ans1(y,v_int_33_749,v_int_33_493')) -->  ans2(x,y,res),

REC CASES
---------
( x=1 & v_int_32_490'=res & 1<=y & b3(y,0,v_int_32_490')) 
  -->  ans(x,y,res)
( v_int_32_490'=res & v_int_32_795=x - 1 & 2<=x & 1<=y & 
  ans(y,v_int_32_795,v_int_32_490')) -->  ans(x,y,res)]


*/
