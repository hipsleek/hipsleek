data node {
  int val;
  node next;
}

bigint<s> == 
  self = null & s = 0 or
  self::node<p, q> * q::bigint<s1> & 0 <= p <= 9 & s = p + 10*s1 & s > 0
  inv s >= 0;

//relation R(int a, int b).  
  
node clone(node x)
  //infer[R]
  //infer[s, s1]
  requires x::bigint<s_123>
  ensures x::bigint<s_123> * res::bigint<s1> & s_123 = s1;
{
  if (x == null)
    return x;
  else
    return new node(x.val, clone(x.next));
}



