data node {
	int val;
	node next;
}



lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1>
	inv n>=0;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv self!=null & tx!=null & n>=1;

coercion "lseg2" self::lseg2<p, n> <- self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;
coercion "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;


void append(node x, node tx, node y, node ty)
	requires x::ll_tail2<tx, n> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, q> & q=m+n;
{
	tx.next = y;
}
