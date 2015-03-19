template int f(int x, int y).
template int g().

data node { int val; node next }

ll<r> == 
	self = null & r = g() or 
	self::node<v, p> * p::ll<r1> & v >= 0 & r = f(v, r1);

int sum (node x)
	infer[f, g]
	requires x::ll<r> & Term[r]
	ensures true;
{
	if (x == null) return 0;
	else return x.val + sum(x.next);
}
