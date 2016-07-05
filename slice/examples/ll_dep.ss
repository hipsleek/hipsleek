data node {
	int val; 
	node next;	
}

/*
// FAILED: Need n1p >= 0 (P) (less info)
// [n2 <- {n1+}]
ll1<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll1<n1p, n2p> & n1 = 1 + n1p & n2p = n2 - n1
	inv n2 >= n1;
*/

/*
// OK (just need n2 = 1 + n1, more info)
ll2<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll2<n1p, n2p> & n1 = 1 + n1p & n2 = 1 + n1
	//self::node<_,p> * p::ll2<n1p, _> & n1 = 1 + n1p & n2 = 1 + n1 // Detecting that n2p is redundant
	inv n2 >= n1;
*/

/*
// OK (enough info)
ll3<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll3<n1p, n2p> & n1 = 1 + n1p & n2 = 2 + n2p
	inv n2 = 2 * n1;
*/

// Prefer constraints at the same level of conseq -> how to predict the needed constraints at different levels

/*
ll4<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll4<n1p, n2p> & n1 = 1 + n1p & n2p = n2 - n1
	inv n1 >= 0 & n2 >= n1;
*/

/*
ll5<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll5<n1p, n2p> & n1 = 1 + n1p & n2 = 1 + n1
	inv n1 >= 0 & n2 >= n1;
*/

ll6<n1, n2> ==
	self = null & n1 = 0 & n2 = 0 or
	self::node<_,p> * p::ll6<n1p, n2p> & n1 = 1 + n1p & n2 = 2 + n2p
	inv n1 >= 0 & n2 = 2 * n1;

n3 = n1 + n2 & n3 >= n2 & n3 <= n1 |- n1 >= 0 & n2 <= 0
	n3 = n1 + n2 & n3 >= n2 |- n1 >= 0
	n3 = n1 + n2 & n3 <= n1 |- n2 <= 0


