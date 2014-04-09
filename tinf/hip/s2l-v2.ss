data node { int val; node next; }

/*
pll<n, s, z> == 
  self = null & n = 0 & s = 0 & z = 0 or
  self::node<v, p> * p::pll<n1, s1, z1> 
		& v >= 0 & n = n1 + 1 & s = s1 + v 
		& (v = 0 & z = z1 + 1 | v != 0 & z = z1)
	inv n >= 0 & s >= 0 & z >= 0;
*/

pll<n, s> == 
  self = null & n = 0 & s = 0 or
  self::node<v, p> * p::pll<n1, s1> 
		& v >= 0 & n = n1 + 1 & s = s1 + v 
	inv n >= 0 & s >= 0;

node s2l (node x)
	//requires x::pll<n, s, z>
	//ensures res::pll<s, s, 0>;

	requires x::pll<n, s>
	ensures res::pll<s, s>;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    return s2l(x.next);
  } else if (x.val == 1) {
		x.next = s2l(x.next);
		return x;
	} else {
		//dprint;
    x.val = x.val - 1;
    x.next = new node(1, x.next);
    return s2l(x);
  }
}
