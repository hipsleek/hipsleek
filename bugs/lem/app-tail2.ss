data node {
	int val;
	node next;
}

/*
ll_tail<tx> == self::node<_, null> & tx=self
	or self::node<_, r> * r::ll_tail<tx> & r!=null;

lseg<p> == self=p
	or self::node<_, r> * r::lseg<p>;
*/

lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1>
	inv n>=0;

ll_tail2<tx, n> == self::lseg2<tx,n-1> * tx::node<_, null> 
  inv n>=1;

/*
ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv self!=null & tx!=null & n>=1;
*/

lemma "lseg2" self::lseg2<p, n> <-> self::lseg2<q, n1>@D * q::lseg2<p, n2>@D & n=n1+n2;

/*
lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;
//lemma "ll_tail2_1" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;
*/

//lemma "composite" self::lseg2<y, n> * y::lseg2<ty, m-1> * ty::node<_, null> <-> self::ll_tail2<ty, m+n>;
//lemma self::lseg2<p, n> -> self::lseg2<q, n-1> * q::node<_, p>;
//lemma "lsegbreakmerge" self::lseg<p> <-> self::lseg<q> * q::lseg<p>;
//lemma "lltail2lseg" self::ll_tail<t> <-> self::lseg<t> * t::node<_, null>;
//lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;

void append(node x, node tx, node y)
	requires x::ll_tail2<tx, n> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, q> & q=m+n;
	//ensures x::lseg2<q,a> * q::lseg2<ty,b> * ty::node<_,null> & a+b+1=m+n;
	//ensures x::lseg2<ty, m+n-1> * ty::node<_, null>;
{
	tx.next = y;
}


node app_head(node x, node y)
  requires x::ll_tail2<tx, n> * y::node<_,_>
  ensures res::ll_tail2<tx, n+1> & res=y;
{
	y.next = x;
        return y;
}

void app_tail(node x, node tx, node y)
  requires x::ll_tail2<tx, n> * y::node<_,_>
  ensures  x::ll_tail2<y, n+1> ;
{
    y.next = null;
    tx.next = y;
}
