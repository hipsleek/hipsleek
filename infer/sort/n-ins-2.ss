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
  requires x::sortA<a> * y::node<v,null>
  ensures  res::sortA<b> & b=min(a,v) ;
/*

 error with bind operation


*/
{
  bind x to (xv,xn) in { 
    bind y to (yv,yn) in {
    if (yv<=xv) {
        yn = x;
        return y;
    } else {
      if (xn==null) xn=y;
      else {
        xn = insert(xn,y);
      };
      return x;
    }
  }}
}










