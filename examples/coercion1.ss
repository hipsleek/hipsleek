data node {
	int val;
	node next;
}

ll0<> == self=null
	or self::node<_, r> * r::ll0<>;

ll1<n> == self=null & n=0
	or self::node<_, r> * r::ll1<n-1>
	inv n>=0;

ll2<n> == self=null & n=0
	or self::node<_, r> * r::ll2<n-1>
	inv n>=0;

ll_tail<tx> == self::node<_, null> & tx=self
	or self::node<_, r> * r::ll_tail<tx> & r!=null;

lseg<p> == self=p
	or self::node<_, r> * r::lseg<p>;// & self != p;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv n>=1;

lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1> // & self != p
	inv n>=0;

/*
lemma self::ll1<n> <-> self::ll2<n>;

void test1(node x) 
	requires x::ll1<n>
	ensures x::ll2<n>;
	requires x::ll2<n>
	ensures x::ll1<n>;
{
}
*/

//lemma self::ll_tail<tx> <-> self::lseg2<tx,_> * tx::node<_,null>;

void test2(node x, node tx)
	requires x::ll_tail<tx>
	ensures  x::ll_tail<tx>;
{
	tx.val = 1;
}

// lemma "lseg2" self::lseg2<p, n> <-> self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;

//lemma "lsegll" self::lseg<null> <- self::lseg<q> * q::lseg<null>;

// lemma "lseg2" self::lseg2<p, n> <-> self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;

//lemma "lseg21" self::lseg2<p, n> & n > 0 -> self::lseg2<r, n1> * r::node<_, q> * q::lseg2<p, n2> & n=n1+n2+1;

//lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;

//lemma self::lseg2<p, n> & n > 0 -> self::lseg2<q, n-1> * q::node<_, p>;

//lemma self::lseg<p> & self != p -> self::lseg<q> * q::node<_, p>;

//lemma "lsegbreakmerge" self::lseg<p> <- self::lseg<q> * q::lseg<p>;

//lemma "lltail2lseg" self::ll_tail<t> <-> self::lseg<t> * t::node<_, null>;

lemma "univ" self::lseg2<p, n> & n=a+b -> self::lseg2<q, a> * q::lseg2<p, b>;
/*
{
//	split a == 0;
//	split b == 0;
	conseq unfold q; (* q is quantified, how do I get its name *)
	return;
}
*/

void prove3(node x, node p, int n, int a, int b)
//	requires x::lseg2<p, n> & a, b >= 0 & n = a + b
	requires x = p & n = 0 & a, b >= 0 & n = a + b
		or x::node<_, r1> * r1::lseg2<p, n-1> & a, b >= 0 & n = a + b
//	ensures q::lseg2<p, b> & x = q & a = 0
//		or x::node<_, r2> * r2::lseg2<q, a - 1> * q::lseg2<p, b>;
	ensures q = p & b = 0 & x = q & a = 0
		or q::node<_, r3> * r3::lseg2<p, b-1> & x = q & a = 0
		or x::node<_, r2> * r2::lseg2<q, a - 1> & q = p & b = 0
		or x::node<_, r2> * r2::lseg2<q, a - 1> * q::node<_, r3> * r3::lseg2<p, b-1>;
{
//	split a == 0;
//	split b == 0;
dprint;
	return;
/*
	if (n == 0) {
		return;
	}
	else {
		return;
	}
*/
}

void prove2(node x, node r, node p)
	requires x::node<_, r> * r::lseg<p>
	ensures x::node<_, p> 
		or x::node<_, s> * s::lseg<q> * q::node<_, p>;
{
	if (r == p) {
		return;
	}
	else {
		node t = x.next;
		if (t == p) {
			return;
		}
		else {
			prove2(t, r.next, p);
		}
	}
}

void prove1(node x, node q, node p)
	requires x::lseg<q> * q::lseg<p>
	ensures x = p or x::node<_, r> * r::lseg<p>;
{
	if (x == q) {
		if (q == p) {
			return;
		}
		else {
			return;
		}
	}

	node t = x.next;

	if (q == p) return;
	else {
		prove1(t, q, p);
	}
}

void tt2(node x)
	requires x::lseg2<y, n> & n > 10 & a = 5
	ensures x::lseg2<r, a> * r::lseg2<y, b>;
{}

void tt1(node x)
	requires x::ll1<a> & b=6 & a=5
	ensures x::ll1<b>;
{}

void tt(node x)
	requires x::lseg2<p, n> & n > 0
	ensures x::lseg2<r, n-1> * r::node<_, p>;
{}

void append(node x, node tx, node y, node ty)
//	requires x::ll_tail<tx> * y::ll_tail<ty>
//	ensures x::ll_tail<ty>;
	requires x::ll_tail2<tx, n> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, m+n>;
{
	tx.next = y;
//	dprint;
}

void test10(node x, node tx)
	requires x::lseg<tx>
	ensures true;
{
	tx.next = null;
}

void test9(node x)
	requires x::lseg2<tx, n> * tx::node<_, y> * y::ll_tail2<ty, m>
	ensures x::ll_tail2<ty, m+n+1>;
{}

void test8(node x)
	requires x::lseg<tx> * tx::node<_, y> * y::ll_tail<ty>
	ensures x::ll_tail<ty>;
{}

void test7(node x)
	requires x::node<_, y> * y::ll_tail<ty>
	ensures x::lseg<ty> * ty::node<_, null> & x!=ty;
	requires x::lseg<ty> * ty::node<_, null> & x!=ty
	ensures x::node<_, y> * y::ll_tail<ty>;
{}

void test3(node x)
	requires x::lseg2<p, n>
	ensures x::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;
{}

void test4(node x)
	requires x::lseg2<q, n1> * q::lseg2<p, n2>
	ensures x::lseg2<p, n1+n2>;
{}

void test5(node x)
	requires x::lseg2<p, n1+1>
	ensures x::lseg2<q, n1> * q::node<_,p>;

	requires x::lseg2<q, n1> * q::node<_,p>
	ensures x::lseg2<p, n1+1>;

    requires x::lseg2<q, n1> * q::node<_, p> * p::lseg2<r, n2>
	ensures x::lseg2<r, n1+n2+1>;
{}


void test6(node x, ref node tx)
	requires x::ll_tail<tx>
	ensures x::ll_tail<_>;
{
	node tmp = new node(10, null);
	tx.next = tmp;
	tx = tmp;
}

lla<n> == self::node<_, r> & n=2
	inv n>=0;

llb<n> == self::node<_, r> & n=3
	inv n>=0;


void test11(node x, node y)
	requires x::node<_, r> * r::node<_,null> * y::node<_,null>
	ensures x::lla<n> * y::llb<n>;
{}
