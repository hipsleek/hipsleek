data node {
	int val;
	node left;
	node right;
}


avl1<n, h> ==
	self = null & h = 0 & n = 0 or
	self::node<_, p, q> * p::avl1<n1, h1> * q::avl1<n2, h2>
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2)
		& -1 <= h1 - h2 <= 1
	inv h >= 0 & n >= 0 & $ n >= h;


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