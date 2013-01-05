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
*************************************
*******pure relation assumption ******
*************************************[RELDEFN R: ( b=v & b<=a) -->  R(b,a,v),
RELDEFN R: ( b=v & b<=a) -->  R(b,a,v),
RELDEFN R: ( a=b & b<v) -->  R(b,a,v),
RELASS [R]: ( R(b_658,a_642,v_643)) -->  (a_642<=b_658 & b_658<=(v_643-2)) | v_643<=(b_658+1),
RELDEFN R: ( a<v) -->  R(b,a,v)]


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










