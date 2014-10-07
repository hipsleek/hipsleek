/* selection sort */

data node {
	int val; 
	node next; 
}

 relation O(int m,int n).

 sortll<mi> == 
    self::node<mi,null>
   or exists O: self::node<mi, p> * p::sortll<m2> & O(mi,m2) & p!=null
 inv self!=null;

node insert(node x, node y)
 infer [O]
 requires y::node<v,null>
 case {
   x=null -> 
      ensures res::sortll<v>;
  x!=null -> 
     requires x::sortll<mn> 
     ensures  res::sortll<w> & w=min(v,mn) ;
  }
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
      x.next=tmp;
      return x;
    }
   }
}










