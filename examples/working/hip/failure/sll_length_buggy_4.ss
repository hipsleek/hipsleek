data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node delete_first(node x)
  requires x::ls<null,n> & n<=1 ensures res=null;
  requires x::node<a,t> * t::ls<null,n> ensures t::ls<null,n> & res=t;
{
  if (x == null)
    return null;
  else if (x.next == null) {
    free(x);
    return x;
  }
  else {
    node y = x.next;
    return x;
  }
}
