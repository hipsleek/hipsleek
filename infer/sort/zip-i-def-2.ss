/* selection sort */

data node {
	int val; 
	node next; 
}

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;

relation R(int a,int b,int c).
relation P(int a,int b).

node zip(node x, node y)
  infer [P,R]
  requires x::llN<a> * y::llN<b> & P(a,b)
  ensures  res::llN<r> & R(a,b,r);
{
  if (x==null) return null;
  else {
    bind x to (xv,xn) in
    {
      bind y to (yv,yn) in
      { xv = xv+yv;
        xn = zip(xn,yn);
      }
    }
    return x;
  }
}

  /*
Checking procedure zip$node~node... 
*************************************
*******pure relation assumption ******
*************************************
[RELASS [P]: ( P(a,b)) -->  (b!=0 | a!=1) & (b!=0 | 2>a),
RELDEFN P: ( a=a_602+1 & b=b_603+1 & 0<=a_602 & 0<=b_603 & P(a,b)) -->  P(a_602,b_603),
RELDEFN R: ( r=0 & a=0 & 0<=b & P(a,b)) -->  R(a,b,r),
RELDEFN R: ( r_617=r-1 & b_603=b-1 & a_602=a-1 & 1<=b & 1<=a & 1<=r & P(a,b) & 
R(a_602,b_603,r_617)) -->  R(a,b,r)]
*************************************

!!! PROBLEM with fix-point calculation
Procedure zip$node~node FAIL-2

Exception Not_found Occurred!

Error(s) detected when checking procedure zip$node~node
 */






