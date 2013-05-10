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

relation Q(int a,int b,int c).
relation P(int a,int b).

node zip(node x, node y)
  infer [P,Q]
  requires x::llN<a> * y::llN<b> & P(a,b)
  ensures  res::llN<r> & Q(a,b,r);
  /*

!!! REL POST :  R(a,b,r)
!!! POST:  a=r & 0<=r & r<=b
!!! REL PRE :  P(a,b)
!!! PRE :  a<=b

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










