data node {
	int val;
	int height;
	node left;
	node right;
}

/*
avl1<n, h> ==
	self = null & h = 0 & n = 0 or
	self::node<_, p, q> * p::avl1<n1, h1> * q::avl1<n2, h2>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
        & -1 <= h1 - h2 <= 1
	inv h >= 0 & n >= 0 & $ n >= h;
*/
/*
avl1<n, h, b> ==
	self = null & h = 0 & n = 0 & b = 0 or
	self::node<_, p, q> * p::avl1<n1, h1, b1> * q::avl1<n2, h2, b2>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
        & ($ b) = h1 - h2
		& -1 <= h1 - h2 <= 1
	inv h >= 0 & n >= 0 & ($ n >= h) & -1 <= b <= 1;
*/

avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
	or self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
		& m = 1+m1+m2 & n = max(n1, n2) + 1 
		// -1 <= n1-n2 <=1 
		& (n2+($ bal)=n1+1) & n2<=n1+1 & n1 <= 1+n2
	inv m >= 0 & n >= 0 & 0<=bal<=2  & /*($ -2+(2*bal)<=n)*/ ($ -2<=n-(2*(bal))) & 
  ($ 2<=(2*( bal))+n)  &  ($ -1+(bal)<=m) & ($ 1<=((bal)+m)) & ($ m >= n);

int height(node x)
	requires x::avl<m, n, bx>
	ensures x::avl<m, n, bx> & res = n;

{
	//dprint;
	if (x == null) {
		assume false;
		return 0;
	}
	else {
		//assume false;
		return x.height;
	}
}


/*
avl2<n, h, c> ==
	self = null & h = 0 & n = 0 & c = 0 or
	self::node<_, p, q> * p::avl2<n1, h1, c1> * q::avl2<n2, h2, c2>
		& n = 1 + ($ n1 + ($ n2))
		& h = 1 + max($ h1, h2)
		& -1 <= h1 - h2 & (h1 - h2 <= 1)
		& c = ($ n) - h
	inv h >= 0 & n >= 0 & c >= 0;
*/