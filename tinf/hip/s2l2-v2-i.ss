template int f().
template int g(int x, int y).

data node {
  int val;
  node next;
}

/*
pll<r> == 
  self = null & r = f() or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = g(v, r1)
  inv r >= 0;
*/

pll<r> == 
  self = null & r = 1 or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = v + r1 - 1;

node s2l (node x)
	//infer[f, g]
  requires x::pll<r> & Term[r]
  ensures true;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    return s2l(x.next);
  } else if (x.val == 1) {
    x.next = s2l(x.next);
    return x;
	} else {
    x.val = x.val - 1;
		//return new node(1, s2l(x));
		x.next = new node(1, x.next);
		return s2l(x);
  }
}
