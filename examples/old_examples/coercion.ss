data node {
	int val;
	node next;
}

lseg<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg<p, n-1> & self!=p
//	inv ex (i: (self=0 & n=0 | self=i & i>0 & n>0));
	inv n>=0;

void lseg1(node x, node p)
	requires x::lseg<p, n>
	ensures x::lseg<r, m> * r::lseg<_, _>;
{
	if (x != p)
		lseg1(x.next, p);
}

void lseg2(node x, node y)
	requires x::lseg<y, n> * y::lseg<p, m>
	ensures x::lseg<p, m+n>; 
{
	if (x != y) {
		lseg2(x.next, y);
	}
/*
	else {
		assert n=0;
		assert x'::lseg<p,m>;
	}
*/
}


bool lseg3(node x, node y)
	requires x::lseg<p, _> * y::lseg<p, _>
	ensures res;
{
	//debug on;
	assert x'=y';
	//debug off;

	return x==y;
}

bool choice() requires true ensures res or !res;
