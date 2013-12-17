template int r1(int n).
template int r2(int n).

data node { int val; node next; }

ll<n> == 
	self = null & n = 0 or
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
infer [r1]
requires x::ll<n> & Term[r1(n)]
ensures res = n;
{
	if (x == null) return 0;
	else return length_aux(x);
}

int length_aux (node x)
infer [r2]
requires x::ll<n> & x!= null & Term[r2(n)]
ensures res = n;
{
	return 1 + length(x.next);
}
