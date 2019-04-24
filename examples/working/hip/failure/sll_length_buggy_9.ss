data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node delete_all(node x)
  requires x::ls<null,n> ensures emp & res=null;
{
  if (x == null)
    return null;
  else {
    node t = x.next;
    delete_all(t);
    return null;
  }
}
