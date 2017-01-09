data node { int val; node next }

ll<s> == 
	self = null & s = 0 or 
	self::node<v, p> * p::ll<s1> & v >= 0 & s = v + s1
	inv s >= 0;

void sum_dec (node x)
	requires x::ll<s> & Term[s]
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
