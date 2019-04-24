data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node delete_last(node x)
  requires x::ls<null,n> & n<=1 ensures res=null;
  requires x::ls<null,n> & n>1 ensures x::ls<null,n-1>;
{
  if (x == null)
    return null;
  else if (x.next == null) {
    return null;
  }
  else if (x.next.next == null)  {
    x.next = null;
    return x;
  }
  else {
    delete_last(x);
    return x;
  }
}
