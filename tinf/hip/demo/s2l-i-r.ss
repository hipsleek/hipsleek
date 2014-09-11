template int f(int x, int y).

data node { int val; node next; }

pll<r> == 
  self = null & r = 0 or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = f(v, r1)
  inv r >= 0;

node s2l (node x)
	infer[f]
  requires x::pll<r> & Term[r]
  ensures res::pll<_> & res = x;
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
