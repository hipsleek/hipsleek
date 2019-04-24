data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node concat(node x, node y)
  requires x::ls<null,n> * y::ls<null,m> & n=0
    ensures res::ls<null,m> & res=y;
  requires x::ls<null,n> * y::ls<null,m> & n>0
    ensures res::ls<null,n+m> & res=x;
{
  if (x == null)
    return x;
  else if (x.next == null) {
    x.next = x;
    return x;
  }
  else {
    concat(x.next, x);
    return x;
  }
}
