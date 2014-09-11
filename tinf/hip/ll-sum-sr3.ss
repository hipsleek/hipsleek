template int f().
template int g(int x, int y).

data node { int val; node next }

ll<r> == 
	self = null & r = f() or 
	self::node<v, p> * p::ll<r1> & v > 0 & r = g(v, r1) // v >= 0: invalid
	;

void sum_dec (node x)
	infer[f, g]
	requires x::ll<r> & Term[r]
	ensures true;
{
	if (x == null) return;
	else if (x.val <= 1)
		sum_dec(x.next);
	else {
		x.val = x.val - 1;
		sum_dec(x);
	}
}
