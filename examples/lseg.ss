data node {
	int val;
	node next;
}

lseg<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg<p, m> & n=m+1
	inv n>=0;
	

lemma lbreak(node x, int n, int n1, int n2, node q)
	requires x::lseg<p, n> & n=n1+n2 & n1>=0 & n2>=0
	ensures x::lseg<q, n1> * q::lseg<p, n2>;

	requires x::lseg<q, n1> * q::lseg<p, n2> & n=n1+n2 & n1>=0 & n2>=0
	ensures x::lseg<p, n>;
{
	if (n1==0) {
		assume q=x;
	}
	else {
		lbreak(x.next, n-1, n1-1, n2, q);
	}
}

/*
lemma lmerge(node x, node y, int n1, int n2)
	requires x::lseg<y, n1> * y::lseg<p, n2>
	ensures x::lseg<p, n> & n=n1+n2;
{
	if (n1==0) {
		assert x=y;
		assume false;
	}
	else assume false;
}
*/

ll_tail<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail<tx, n-1> & r!=null
	inv n>=1;

lemma ll_tail1(node x)
	requires x::ll_tail<tx, n>
	ensures x::lseg<tx, n-1> * tx::node<_, null>;

//	requires x::lseg<tx, n> * tx::node<_, null>
//	ensures  x::ll_tail<tx, n+1>;
{
	if (x.next != null) {
		ll_tail1(x.next);
	}
}

void add(node x, node tx, node y)
	requires x::ll_tail<tx, n> * y::node<_, _>
	ensures x::ll_tail<y, n+1>;
{
	//ll_tail1(x);

	tx.next = y;
	y.next = null;
	//tx = y;
	
	dprint;
}
