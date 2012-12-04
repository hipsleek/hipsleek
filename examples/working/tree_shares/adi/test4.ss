data cl { int val; }

macro L == (#,)
macro R == (,#)

Barrier bn[2]<int state, cl a, int A> == [
	(0,1,[
		requires a::cl<A> * self::bn(@@R)<0, a, A>
		 ensures self::bn(@@R)<1, a, A>;,
		requires self::bn(@@L)<0, a, A>
		 ensures a::cl<A> * self::bn(@@L)<1, a, A>;])
	];


void th1 (cl a, barrier b1)
	requires a::cl<0> * b1::bn(@@R)<0, a, 1>
	 ensures b1::bn(@@R)<1, a, 1>;
{
	a.val = a.val + 1;
	Barrier b1;
}

void th2 (cl a, barrier b1, barrier b2)
	requires b1::bn(@@L)<0, a, 1> * b2::bn(@@R)<0, a, 2>
	 ensures b1::bn(@@L)<1, a, 1> * b2::bn(@@R)<1, a, 2>;
{
	Barrier b1;
	a.val = a.val + 1;
	Barrier b2;
}

void th3 (cl a, barrier b2)
	requires b2::bn(@@L)<0, a, 2>
	 ensures a::cl<3> * b2::bn(@@L)<1, a, 2>;
{
	Barrier b2;
	a.val = a.val + 1;
}

