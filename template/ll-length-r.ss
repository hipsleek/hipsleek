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

/*

**** TEMPLATE ASSUMPTION ****
[ n=fr( v_946, n1_948) & n1_948=n_952 --> (r( n))>(r( n_952))
, 0<=n --> 0<=(r( n))
, n=fr( v_897, n1_896) & 0<=n1_896 --> 0<=n
, n=fb() --> 0<=n
]
**** TEMPLATE INFERENCE RESULT ****
[ template int r(int n) == 2+(1*n), 
template int fb() == 2, 
template int fr(int v,int n) == 3+(0*v)+(1*n)]

Looks good, though I was wondering
if we could support a more minimalistic outcome?

   fb() = 0
   fr(v,n) = 1+1*n
   r(n) = 0+1*n

*/
