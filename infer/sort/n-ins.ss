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
  ensures  res::sortA<b> & b=min(c,v); 
    //(b=a | v<a & b=v); 
    //(b=a | b=v);
/*
  infer [R]
  requires x::sortA<v> * y::node<v,null>
  ensures  res::sortA<b> & R(b,a,v);
*************************************
*******pure relation assumption ******
*************************************
[RELDEFN R: ( b=v) -->  R(b,a_649,v),
RELDEFN R: ( b=v) -->  R(b,a_686,v)]
*************************************
What happen to the recursive cases?

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










