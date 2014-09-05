template int f().
template int g(int x, int y).

data node { int val; node next; }

pll<n, s> == 
  self = null & n = 0 & s = 0 or
  self::node<v, p> * p::pll<n1, s1> & v >= 0 & n = n1 + 1 & s = s1 + v
	inv n >= 0 & s >= 0;

/*
pll<r> == 
  self = null & r = f() or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = g(v, r1)
	inv r >= 0;
*/

node s2l (node x)
	infer[g]
	requires x::pll<n, s> & Term[g(n, s)]
	ensures res::pll<s, s>;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    return s2l(x.next);
  } else if (x.val <= 1) {
		x.next = s2l(x.next);
		return x;
	} else {
    x.val = x.val - 1;
    x.next = new node(1, x.next);
    return s2l(x);
  }
}
