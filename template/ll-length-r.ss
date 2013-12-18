template int fr(int v, int n). // REC
template int fb(). // BASE
template int r(int n).


data node { int val; node next; }

/* Raw version of ll: n will be automatically added.
ll<> ==
	self = null or
	self::node<v, p> * p::ll<n1>;
*/

ll<n> ==
	self = null & n = fb() or
	self::node<v, p> * p::ll<n1> & n = fr(v, n1)
	inv n >= 0;

int length (node x)
infer [r, fr, fb]
requires x::ll<n> & Term[r(n)]
ensures res >= 0;
{
	if (x == null) return 0;
	else {
		return 1 + length(x.next);
	}
}


