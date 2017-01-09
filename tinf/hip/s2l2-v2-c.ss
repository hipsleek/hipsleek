template int f(int x, int y).

data node { int val; node next; }

pll<n, s, r> == 
  self = null & n = 0 & s = 0 & r = 0 or
  self::node<v, p> * p::pll<n1, s1, r1> & v >= 0 
    & n = n1 + 1 & s = s1 + v
    & r = f(v, r1) 
  inv n >= 0 & s >= 0 & r >= 0;

node s2l (node x)
  infer[f]
  requires x::pll<n, s, r> & Term[r]
  ensures res::pll<s, s, _>;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    return s2l(x.next);
  } else if (x.val == 1) {
    x.next = s2l(x.next);
    return x;
  } else {
    x.val = x.val - 1;
    x.next = new node(1, x.next);
    return s2l(x);
  }
}
