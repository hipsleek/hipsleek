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


node zip(node x, node y)
  requires x::llN<a> * y::llN<b> & a<=b
  ensures  res::llN<a> ;
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










