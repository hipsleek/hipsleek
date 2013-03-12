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
!!! REL POST :  R(b,a,v)
!!! POST:  (b=v & v<=a) | (a=b & b<v)

  infer [R]
  requires x::sortA<v> * y::node<v,null>
  ensures  res::sortA<b> & R(b,a,v);

!!! REL POST :  R(b,a_650,v)
!!! POST:  b=v
  
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & b=min(a,v); 
    //(b=a | v<a & b=v); 
    //(b=a | b=v);

*/
{
    if (y.val<=x.val) {
        y.next = x; return y;
    } else {
      if (x.next==null) x.next=y;
      else {
        x.next = insert(x.next,y);
      };
      return x;
    }
}










