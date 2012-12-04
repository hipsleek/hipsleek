data cl { int val; }

macro L == (#,)
macro R == (,#)

Barrier bn[2]<int state, cl a, int A> == [
	(0,1,[
		requires a::cl<A> * self::bn(@@L)<0, a, A>
		 ensures self::bn(@@L)<1, a, A>;,
		requires self::bn(@@R)<0, a, A>
		 ensures a::cl<A> * self::bn(@@R)<1, a, A>;]),
	(1,2,[
		requires self::bn(@@L)<1, a, A>
		 ensures a::cl(@@L)<A> * self::bn(@@L)<2, a, A>;,
		requires a::cl<A> * self::bn(@@R)<1, a, A>
		 ensures a::cl(@@R)<A> * self::bn(@@R)<2, a, A>;])
	];

void th1 (cl a, barrier b)
	requires a::cl<0> * b::bn(@@L)<0, a, 0>
	 ensures a::cl(@@L)<0> * b::bn(@@L)<2, a, 0>;
{
	a.val = a.val + 1;
	Barrier b;
	Barrier b;
}

void th2 (cl a, barrier b)
	requires b::bn(@@R)<0, a, 0>
	 ensures a::cl(@@R)<0> * b::bn(@@R)<2, a, 0>;
{
	Barrier b;
	a.val = a.val - 1;
	Barrier b;
}
