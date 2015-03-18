template int f().
template int g(int x, int y).

data node {
  int val;
  node next;
}

pll<r> == 
  self = null & r = f() or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = g(v, r1)
  inv r >= 0;

/*
pll<r> == 
  self = null & r = 0 or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = 4 + 4*v + r1
  inv r >= 0;
*/

node s2l (node x)
	infer[f, g]
  requires x::pll<r> & Term[r]
  //ensures res::pll<r>; // g(x, y) = 4 + 4x + y
	ensures true; // g(x, y) = 1 + x + y
{
  if (x == null) return x;
  else if (x.val <= 0) {
    x.next = s2l(x.next);
    return x;
  } else {
    x.val = x.val - 1;
    //x.next = new node(0, x.next);
    //return s2l(x);
		return new node(0, s2l(x));
  }
}
