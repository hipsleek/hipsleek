/* selection sort */

data node {
	int val; 
	node next; 
}

relation O(int m, int n).

/*
sortll<mi> == self::node<mi, null> or
  self::node<mi, p> * p::sortll<m2> & O(mi,m2)
inv self!=null;
*/

sortll<mi> == self=null & mi=\inf
 or self::node<mi, p> * p::sortll<m2> & mi<=m2
inv true;

node insert(node x, node y)
     requires x::sortll<mn> * y::node<v,null>
     ensures  res::sortll<w> & w=min(v,mn) ;
{
  if (x==null) return y;
  else {
    int t = x.val;
    if (y.val<=x.val) {
        y.next = x;
        return y;
    } else {
      node tmp;
      tmp = insert(x.next,y);
      //assume tmp'=null or tmp'!=null;
      x.next=tmp;
      return x;
    }
   }
}










