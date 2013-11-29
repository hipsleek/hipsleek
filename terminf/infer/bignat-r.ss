data node {
  int val;
  node next;
}

bigint<> == 
  self = null or
  self::node<p, q> * q::bigint<> & 0 <= p <= 9;

node clone(node x)
  requires x::bigint<>
  ensures x::bigint<> * res::bigint<>;
{
  if (x == null) return x;
  return new node(x.val, clone(x.next));
}
