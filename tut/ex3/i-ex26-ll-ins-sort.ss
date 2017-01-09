data node {
  int val;
  node next;
}

lsort<n, S> == emp & self=null & n=0 & S={} 
  or self::node<v,q>*q::lsort<n1, S1> & n=n1+1 & 
     S=union({v},S1) & forall (w:(w notin S1| v<=w))
  inv true;

node insert(node x, node y)
  infer[@term]
  requires x::node<v,_> * y::lsort<n, S>
  ensures res::lsort<n+1, S2> & S2=union({v},S);
{
  if (y==null) {x.next=null; return x;}
  else 
    if (x.val<=y.val) {
      x.next=y; return x;
    } else {
      node tmp = insert(x,y.next);
      y.next = tmp;
      return y;
    }
}

