/* selection sort */

data node {
	int val; 
	node next; 
}

// needs infinity
sortA<v> == self::node<v,null> 
 or self::node<v, p> * p::sortA<v2> & v<=v2 
inv self!=null;

relation R(int r, int a, int b).

node insert(node x, node y)
  infer [R]
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & R(b,a,v);
/*
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & b=min(a,v) ;

!!! REL POST :  R(b,a,v)
!!! POST:  (b=v & v<=a) | (a=b & b<v)
!!! REL PRE :  true
!!! PRE :  true

*/
{
  bind x to (xv,xn) in { 
     if (y.val<=xv) {
        y.next = x;
        return y;
    } else {
      if (xn==null) xn=y;
      else {
        xn = insert(xn,y);
      };
      return x;
  }}
}










