data node {
	int val;
	node next;
}

ll_tail<tx> == self::node<_, null> & tx=self
	or self::node<_, r> * r::ll_tail<tx> & r!=null;

lseg<p> == self=p
	or self::node<_, r> * r::lseg<p>;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv n>=1;

lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1>
	inv n>=0;

coercion "lseg2" self::lseg2<p, n> <-> self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;

coercion "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;

//coercion self::lseg2<p, n> -> self::lseg2<q, n-1> * q::node<_, p>;

coercion "lsegbreakmerge" self::lseg<p> <-> self::lseg<q> * q::lseg<p>;

coercion "lltail2lseg" self::ll_tail<t> <-> self::lseg<t> * t::node<_, null>;

void append(node x, node tx, node y, node ty)
//	requires x::ll_tail<tx> * y::ll_tail<ty>
//	ensures x::ll_tail<ty>;
	requires x::ll_tail2<tx, n> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, m+n>;
{
	tx.next = y;
}
