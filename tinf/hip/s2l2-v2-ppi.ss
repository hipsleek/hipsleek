template int f1(int x, int y).
template int f2(int x, int y).
template int g(int x, int y).

data node { int val; node next; }

/* piecewise ranking function - is it amortized? */

pll<r> == 
  self = null & r = 0 or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = g(v, r1)
	inv r >= 0;

node s2l (node x)
	infer[g]
  requires x::pll<r> & Term[r]
	ensures true;
{
  if (x == null) return x;
  else if (x.val <= 0) {
		// v <= 0 --> r = a1*v + b1*r1 + c1
    return s2l(x.next);
  } else if (x.val == 1) {
		// v = 1 --> r = a2*v + b2*r1 + c2
    x.next = s2l(x.next);
    return x;
	} else {
		// v > 1 --> r = a3*v + b3*r1 + c3
    x.val = x.val - 1;
		x.next = new node(1, x.next);
		// r' = a3*(v-1) + b3*(a2*1 + b2*r1 + c2) + c3, v-1 > 1
		// r' = a2*1 + b2*(a2*1 + b2*r1 + c2) + c2, v-1 = 1
		return s2l(x);
  }
}
