template int g(int x).

data node { int val; node next }

ll<s, r> == 
	self = null & s = 0 & r = g(s) or 
	self::node<v, p> * p::ll<s1, r1> & v >= 0 & r = f(v, s1, r1);

int sum (node x)
	infer[f, g]
	requires x::ll<r> & Term[r]
	ensures true;
{
	if (x == null) return 0;
	else return x.val + sum(x.next);
}
