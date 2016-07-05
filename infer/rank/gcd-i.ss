ranking term_r(int x, int y).

int gcd (int x, int y)
infer @pre [term_r] 
requires x>0 & y>0
case {
  x=y -> requires Term[] ensures true;
  x!=y -> requires Term[/* x+y */ term_r(x,y)] ensures true;
}

{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}

/*
BOUNDED
=======
( 1<=y & y<x | 1<=x & x<y) -->  (term_r(x,y))>=0, 
  ==>  r[1]>=1; r[2]>=1

term_r(x,y) = a*x+b*y
 --> a=1, b=1

DECREASING
==========
( x=v_int_13_467'+y' & y=y' & 1<=y' & y'!=v) 
   -->  (term_r(x,y))>(term_r(v,y')), 
( x'=x & y=x+v & 1<=x & v!=x)
   -->  (term_r(x,y))>(term_r(x',v))]

ANALYSIS
========
   1: r(x,y)>r(v,y') [r[1]->r[1]:DEC(?) ; r[2]->r[2]:NC ]
   2: r(x,y)>r(x',v) [r[1]->r[1]:NC ; r[2]->r[2]:DEC(?) ]


  term_r(x,y) = x+y


*/
