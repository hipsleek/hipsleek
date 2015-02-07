data node {
  int val;
  node next;
}

/*
lsortI<m> == self::node<m,null>
  or self::node<m,q>*q::lsortI<m2> & m<=m2
  inv self!=null;
*/

lsortI<m> == self=null & m=\inf
  or self::node<m,q>*q::lsortI<m2> & m<=m2 
  inv true;

node insert(node x, node y)
  requires x::node<v,null> * y::lsortI<mm> 
  ensures res::lsortI<r> & r=min(v,mm);

{
  if (y==null) {
    //assume false;
     return x;
  }
  else 
    if (x.val<=y.val) {
      x.next=y; return x;
    } else {
      node tmp = insert(x,y.next);
      y.next = tmp;
      return y;
    }
}

/*
# ex21-ins-sort-inf.ss --en-inf

*/
