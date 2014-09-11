template int f().
template int g(int x, int y).

data node { int val; node next }

/*
ll<r> == 
	self = null & r = f() or 
	self::node<v, p> * p::ll<r1> & v >= 0 & r = g(v, r1)
	inv r >= 0;
*/

ll<r> ==
	self = null & r = 0 or
	self::node<v, p> * p::ll<_> & v >= 0 & r = v
	inv r >= 0;

void sum_dec (node x)
	//infer[f, g]
	requires x::ll<r> & Term[r]
	ensures true;
{
	if (x == null) return;
	else if (x.val == 0)
		//sum_dec(x.next);
		return;
	else {
		x.val = x.val - 1;
		sum_dec(x);
	}
}
