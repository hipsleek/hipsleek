data cl { int val; }

macro L == (#,)
macro R == (,#)

Barrier bn[2]<int state, cl a1, cl a2, int A1, int A2> == [
	(0,1,[
		requires a1::cl<A1> * self::bn(@@L)<0, a1, a2, A1, A2>
		 ensures a2::cl<A2> * self::bn(@@L)<1, a1, a2, A1, A2>;,
		requires a2::cl<A2> * self::bn(@@R)<0, a1, a2, A1, A2>
		 ensures a1::cl<A1> * self::bn(@@R)<1, a1, a2, A1, A2>;]),
	(1,2,[
		requires a2::cl<A2> * self::bn(@@L)<1, a1, a2, A1, A2>
		 ensures a1::cl(@@L)<A1> * a2::cl(@@L)<A2> *
			 self::bn(@@L)<2, a1, a2, A1, A2>;,
		requires a1::cl<A1> * self::bn(@@R)<1, a1, a2, A1, A2>
		 ensures a1::cl(@@R)<A1> * a2::cl(@@R)<A2> *
			 self::bn(@@R)<2, a1, a2, A1, A2>;])
	];

void th1 (cl a1, cl a2, barrier b)
	requires a1::cl<0> * b::bn(@@L)<0, a1, a2, 0, 0>
	 ensures a1::cl(@@L)<0> * a2::cl(@@L)<0> * b::bn(@@L)<2, a1, a2, 0, 0>;
{
	a1.val = a1.val + 1;
	Barrier b;
	a2.val = a2.val - 1;
	Barrier b;
}

void th2 (cl a1, cl a2, barrier b)
	requires a2::cl<0> * b::bn(@@R)<0, a1, a2, 0, 0>
	 ensures a1::cl(@@R)<0> * a2::cl(@@R)<0> * b::bn(@@R)<2, a1, a2, 0, 0>;
{
	a2.val = a2.val + 1;
	Barrier b;
	a1.val = a1.val - 1;
	Barrier b;
}
