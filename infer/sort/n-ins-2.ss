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
  requires x::sortA<v> * y::node<v,null>
  ensures  res::sortA<b> & R(b,a,v);
/*
  requires x::sortA<v> * y::node<v,null>
  ensures  res::sortA<b> & b=min(a,v) ;
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R: ( b=v) -->  R(b,a_649,v),
RELDEFN R: ( b=v) -->  R(b,a_686,v)]
*************************************
What happen to the recursive cases?

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










