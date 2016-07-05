data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
     self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p & v>0
     inv v >= 0;



node bigint_of(int v)
  requires v >= 0
  ensures true;
{
  if (v < 10) 
    if (v==0) return null;
    else return new node(v,null);
  else return add_node(v, null);  // syntax error here!
  return null;

}

node add_one_digit(node x, int c)
  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;
