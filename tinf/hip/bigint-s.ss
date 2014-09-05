template int f(int x, int y).
template int g(int x, int y).

data node { int val; node next; }

/*
bigint<r> == 
	self = null & r = 0 or
	self::node<p, q> * q::bigint<r1> & 0 <= p <= 9 & r = f(p, r1)
	inv r >= 0;
*/

bigint<r> == 
	self = null & r = 0 or
	self::node<p, q> * q::bigint<r1> & 0 <= p <= 9 & r = p + 10*r1 & r > 0
	inv r >= 0;

node clone(node x)
  requires x::bigint<r> & Term
  ensures x::bigint<r> * res::bigint<r>;

node add_one_digit(node x, int c)
  requires x::bigint<r> & 0 <= c <= 9 & Term
  ensures res::bigint<r + c> * x::bigint<r>;

node karatsuba_mult(node x, node y)
  requires x::bigint<r1> * y::bigint<r2> & Term[r1]
  ensures true;
{
  if (x == null || y == null) return null;
  if (x.next == null || y.next == null) return null; //mult(x, y);
  // x = x1*10+x2
  // y = y1*10+y2
  // A = x1*y1
  //node A = karatsuba_mult(x.next, y.next);
  // B = x2*y2
  //node B = bigint_of(x.val * y.val);
  // C = (x1+x2)*(y1+y2)
  node C = karatsuba_mult(add_one_digit(x.next, x.val), add_one_digit(y.next, y.val));
  // K = C - A - B = x1*y2 + x2*y1
  //node K = sub(C, add(A, B));
  // node K = add(mult_c(x.next, y.val, 0), mult_c(y.next, x.val, 0));
  // x * y = A*100 + K*10 + B
  //return add(shift_left(shift_left(A)), add(shift_left(K), B));
	return null;
}
