template int f().
template int g(int x, int y).

data node { int val; node next; }

pll<r> == 
  self = null & r = f() or
  self::node<v, p> * p::pll<r1> & v >= 0 & r = g(v, r1)
	inv r >= 0;

node s2l (node x)
	infer[f, g]
  //requires x::pll<n, s> & Term[n, s]
	//ensures res::pll<n + s, 0> & res = x;
	requires x::pll<r> & Term[r]
  //ensures res::pll<_> & res = x;
	ensures true;
{
  if (x == null) return x;
  else if (x.val <= 0) {
    x.next = s2l(x.next);
    return x;
  } else {
		int temp = x.val - 1;
    x.val = temp;
    x.next = new node(temp, x.next);
    return s2l(x);
  }
}
