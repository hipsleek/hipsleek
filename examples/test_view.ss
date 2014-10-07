data node {
	int val;
	node next;
}

/*
ll<> == self=null
	or self::node<_, r> * r::ll<>;
*/

/*
sll1<n> == self=null & n=0
		or self::node<_, r> * r::sll1<n-1>;
*/

/*
sll<n> == self=null & n=0
		or self::node<_, r> * r::sll<n-1>
	inv n>=0;
*/

/*
lseg<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg<p, n-1> & self!=p;
*/

/*
lseg1<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg1<p, n-1> & self!=p
	inv n>=0;
*/

ll_tail<n, tx> == self=null & tx=null & n=0
	or self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail<n-1, tx> & r!=null & self!=tx
	inv n>=0;

/*
	without self!=x in the third branch, the following invariant also won't work

	inv	(	self=null & n=0 & tx=null
		|	self=tx & n=1 & self!=null
		|	self!=null & self!=tx & n>1);
*/

/*
even_ll<n> == self=null & n=0
	or self::node<_, r> * r::even_ll<
*/

/*
node f(node x, node y) 
	requires x::sll<n>
	ensures res::sll<n>;
{
	return x;
}
*/