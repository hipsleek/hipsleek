data node {
	int val;
	node next;
}

data node2 {
	bool val;
	node2 prev;
	node2 next;
}

data node3 {
	node val;
	node2 left;
	node2 right;
}

/*

ll<n> == self=null & n=0
	or self::node<v, r> * r::ll<m> & n=m+1 & b=c & c=a & b=self;

node2_v<p, n> == self=null & n=0
	or self::node2<b, p, r> * r::node2_v<self, n-1> & b
	or self::node2<b, p, r> * r::node2_v<self, n>;

node2_v2<p, n> == self=null & n=0
	or self::node2<b, p, r> * r::node2_v2<self, m> & (b & m=n-1 | !b & m=n);
*/

test_view1<> == self::node3<v, l, r>
	or self::node3<_, _, v>;

ll2<n> == self::node<_, null> & n=1
	or self::node<v, r> * r::ll2<n-1>;

ll1<n> == self=null & n=0
	or self::node<v, r> * r::ll<n-1>;

ll<n> == self=null & n=0
	or self::node<v, r> * r::ll<m> & n=m+1;

node3_v4<b> == self::node3<a, b, r> * r::node2<d, b, e>;

node3_v3<> == self::node3<a, b, r> * r::node2<_, b, _>;

node3_v2<a> == self::node3<a, b, b>;

node3_v1<> == self::node3<a, b, b>;
