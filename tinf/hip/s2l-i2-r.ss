data node { int val; node next; }

/*
pll<r1, r2> == 
  self = null & r1 = 0 & r2 = 0 or
  self::node<v, p> * p::pll<rp1, rp2> & v >= 0 & r1 = 1 + v + rp1 & r2 = v + rp2
	inv r1 >= 0 & r2 >= 0;
*/

pll<r> == 
  self = null & r = 0 or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = 1 + 2*v + r1
	inv r >= 0;

node s2l (node x)
  //requires x::pll<r1, r2> & Term[r1, r2]
	requires x::pll<r> & Term[r]
	ensures true;
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
