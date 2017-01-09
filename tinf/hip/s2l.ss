data node {
  int val;
  node next;
}

pll<n, s> == 
  self = null & n = 0 & s = 0 or
  self::node<v, p> * p::pll<n1, s1> & v >= 0 & n = n1 + 1 & s = s1 + v
  inv n >= 0 & s >= 0;

node s2l (node x)
  requires x::pll<n, s> & Term[s, n]
	//requires x::pll<n, s> & Term[n, s] // not valid
  ensures res::pll<n + s, 0> & res = x;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    x.next = s2l(x.next);
    return x;
  } else {
    x.val = x.val - 1;
    x.next = new node(0, x.next);
    return s2l(x);
  }
}
