template int f(int x, int y).
template int g(int x, int y).

data node { int val; node next; }

bigint<r> == 
	self = null & r = 0 or
	self::node<p, q> * q::bigint<r1> & 0 <= p <= 9 & r = p + 10*r1 & r > 0
	inv r >= 0;

node clone(node x)
  requires x::bigint<r> & Term
  ensures x::bigint<r> * res::bigint<r>;

node add_one_digit(node x, int c)
/*
	infer[f]
  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<f(v, c)> * x::bigint<v>;
*/
//infer[@term]
  requires x::bigint<v> & 0 <= c <= 9 & Term[r]
  ensures res::bigint<v+c> * x::bigint<v>;
{
  if (x == null) {
    if (c == 0) return null;
    return new node(c, null);
  }
  int t = x.val + c;
  if (t >= 10) return new node(t - 10, add_one_digit(x.next, 1));
  return new node(t, clone(x.next));
}

/*
# bigint-a.ss

went into a loop!
//infer[@term]
  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;

*/
