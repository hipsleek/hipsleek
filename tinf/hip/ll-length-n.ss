template int r(int x).

data node { int val; node next }

ll<n> == 
	self = null & n = 0 or 
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
	infer[r]
	requires x::ll<n> & Term[r(n)]
	ensures true;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
