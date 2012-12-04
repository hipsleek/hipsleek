data cl { int val; }

macro L == (#,)
macro R == (,#)

Barrier bn[2]<int state, cl a> == [
	(0,1,[
		requires a::cl<A> * self::bn(@@R)<0, a>
		 ensures self::bn(@@R)<1, a>;,
		requires self::bn(@@L)<0, a>
		 ensures a::cl<A> * self::bn(@@L)<1, a>;])
	];


void th1 (cl a, barrier b1)
	requires a::cl<_> * b1::bn(@@R)<0, a>
	 ensures b1::bn(@@R)<1, a>;
{
	a.val = a.val + 1;
	Barrier b1;
}

void th2 (cl a, barrier b1, barrier b2)
	requires b1::bn(@@L)<0, a> * b2::bn(@@R)<0, a>
	 ensures b1::bn(@@L)<1, a> * b2::bn(@@R)<1, a>;
{
	Barrier b1;
	a.val = a.val + 1;
	Barrier b2;
}

void th3 (cl a, barrier b2)
	requires b2::bn(@@L)<0, a>
	 ensures a::cl<_> * b2::bn(@@L)<1, a>;
{
	Barrier b2;
	a.val = a.val + 1;
}

