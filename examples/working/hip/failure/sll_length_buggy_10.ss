data node {
  int val;
  node next;
}

ls<y,n> == self=y & n=0
  or self::node<_, r> * r::ls<y,n2> & n=1+n2;

node insert_first(node x , int a)
  requires x::ls<null,n>
  ensures res::ls<null,n+1>;
{
  node u = new node(a, null);
  return u;
}
