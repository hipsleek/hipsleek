data node {
  int val;
  node next;
}

/*
 lsort<S> == emp & self=null & S={}
  or self::node<v,q>*q::lsort<S1> & S=union({v},S1)
          & forall (w:(w notin S1| v<=w))
  inv true;
*/

lsortI<m> == self::node<m,null>
  or self::node<m,q>*q::lsortI<m2> & m<=m2
  inv self!=null;


void swap(node x, node y)
  requires x::node<v,null> * y::node<w,null>
  ensures  x::node<w,null> * y::node<v,null>;
{
  int tmp = x.val;
  x.val=y.val;
  y.val=tmp;
}

/*
# ex20a-staged.ss

 (i) this spec cannot be staged
 (ii) can you weaken the pre-cond?

*/
