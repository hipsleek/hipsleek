data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> & n=1 & r=null
	or self::node<_, r> * r::ll<n-1> & r!=null
	inv n>=0;

void test(node x)
	requires x::node<_, r> * r::ll<n>
	ensures x::ll<n+1>;
{}
