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

  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & b=min(a,v) ;

/* 
 why does this example succeed individually
 but fails when put together? 
 esp when infernce is done before checking
 Is this due to us modifying the spec after inference?
 Maybe we need to re-think on this.

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










