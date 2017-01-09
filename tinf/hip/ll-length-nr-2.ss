template int f(int x).
template int g(int x, int y, int z).

data node { int val; node next }

ll<n, r> == 
	self = null & n = 0 & r = f(n) or 
	self::node<v, p> * p::ll<n1, r1> & n = n1 + 1 & r = g(v, n1, r1)
	inv n >= 0;

int length (node x)
	infer[f, g]
	requires x::ll<n, r> & Term[r]
	ensures true;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
