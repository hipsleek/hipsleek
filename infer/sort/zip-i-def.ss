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
  infer [R]
  requires x::llN<a> * y::llN<b> & a<=b
  ensures  res::llN<r> & R(a,b,r);
  /*
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN P: 
( a=a_603+1 & b=b_604+1 & 0<=a_603 & 0<=b_604 & P(a,b)) 
   -->  P(a_603,b_604),
RELDEFN R: 
( r_619=r-1 & b_604=b-1 & a_603=a-1 & 1<=b & 1<=a & 1<=r & P(a,b) & 
  R(a_603,b_604,r_619)) -->  R(a,b,r)]
*************************************
fixcalc: subrec: found different no of QSVs for CAbst:
 P(a,b)
 
 PROBLEM: What happen to the base-cases for R(..)?
 */
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










