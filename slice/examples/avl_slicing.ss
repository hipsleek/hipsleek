data node {
	int val;
	node left;
	node right;
}

// 1<=h & h<=n |-  0<=h
avl<n, h> ==
	self = null & h = 0 & n = 0 or
	self::node<_, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& n = 1 + n1 + n2 & h = 1 + max(h1, h2) & -1 <= h1 - h2 <= 1
	inv h >= 0 & n >= 0 & n >= h;

/*
// FAIL: true |- h <= n (inv true & ["n": n >= 0; "h": h >= 0; "nh": n >= h];)
avl<n, h> ==
	self = null & ["n": n = 0; "h": h = 0] or
	self::node<_, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& ["n": n = 1 + n1 + n2; "h": h = 1 + max(h1, h2) & -1 <= h1 - h2 <= 1]
	inv true & ["n": n >= 0; "h": h >= 0; "nh": n >= h];
*/
/*
avl<"n": n, "h": h> ==
	self = null & ["n": n = 0; "h": h = 0] or
	self::node<_, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& ["n": n = 1 + n1 + n2; "h": h = 1 + max(h1, h2) & -1 <= h1 - h2 <= 1]
	inv true & ["n": n >= 0; "h": h >= 0 & n >= h];
*/
/*
avl<n, h> ==
	self = null & ["nh": n = 0 & h = 0] or
	self::node<_, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& ["nh": n = 1 + n1 + n2 & h = 1 + max(h1, h2)]
	inv true & ["nh": n >= h & n >= 0 & h >= 0];
*/
/*
// 1<=h |-  0<=h
// FAIL: self=null & h=0 & n=0 | self!=null & 1<=h & 1<=n |- n>=h
// Do not add the constraints n1 >= h1 & n2 >= h2 into the ante
avl<n, h> ==
	self = null & h = 0 & n = 0 or
	self::node<_, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& n = 1 + n1 + n2 & h = 1 + max(h1, h2)
	inv h >= 0 & n >= 0 & ["": n >= h];
*/
/*
avl<n1, n2> ==
	self = null & n1 = 0 & n2 = 1 or
	self::node<_, p, q> * p::avl<n1p, n2p> * q::avl<n1q, n2q> &
		n1 = 1 + n1p + n1q & n2 = n1 + 1
	inv n1 >= 0 & n2 >= n1;
*/
