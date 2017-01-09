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


node insert(node x, node y)
 case {
  y=null ->
    requires x::node<v,null> 
    ensures  res::lsortI<v>;
  y!=null ->
    requires x::node<v,null> * y::lsortI<m> 
    ensures res::lsortI<min(v,m)>;
 }
{
  if (y==null) return x;
  else 
    if (x.val<=y.val) {
      x.next=y; return x;
    } else {
      node tmp = insert(x,y.next);
      y.next = tmp;
      return y;
    }
}

