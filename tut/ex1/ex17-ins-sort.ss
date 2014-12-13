data node {
  int val;
  node next;
}

lsort<S> == emp & self=null & S={}
  or self::node<v,q>*q::lsort<S1> & S=union({v},S1)
          & forall (w:(w notin S1| v<=w))
  inv true;

node insert(node x, node y)
  requires x::node<v,_> * y::lsort<S>
  ensures res::lsort<S2> & S2=union({v},S);
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

