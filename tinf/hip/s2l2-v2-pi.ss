template int f1(int x, int y).
template int f2(int x, int y).
template int f(int x, int y).
template int g(int x, int y).

data node { int val; node next; }

/* piecewise ranking function - is it amortized? */

pll<n, s, r> == 
  self = null & n = 0 & s = 0 & r = 0 or
  self::node<v, p> * p::pll<n1, s1, r1> & v >= 0 
		& n = n1 + 1 & s = s1 + v
		//& (v <= 0 & r = 1 + r1 | v = 1 & r = 1 + r1 | v > 1 & r = 2*v + r1)
		//& (v <= 1 & r = 1 + r1 | v > 1 & r = 2*v + r1)
		//& (v <= 0 & r = 1 + r1 | v = 1 & r = 1 + r1 | v > 1 & r = f2(v, r1))
    & r = f(v, r1) 
	inv n >= 0 & s >= 0 & r >= 0;

node s2l (node x)
	infer[f2]
  requires x::pll<n, s, r> & Term[r]
  ensures res::pll<s, s, _>;
	//ensures true;
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
