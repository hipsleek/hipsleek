
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}
data cl2{int x;}

macro BC == (#,) 
macro B1 == (,(#,)) 
macro B2 == (,(,(#,)))
macro B3 == (,(,(,(#,))))
macro B4 == (,(,(,(,#))))
macro D1 == (#,)
macro D2 == (,(#,)) 
macro D3 == (,(,(#,)))
macro D4 == (,(,(,#)))
macro D1W == (,#)
macro D2W == (#,(,#))
macro D3W == (#,(#,(,#)))
macro D4W == (#,(#,(#,)))

void f1(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;
void f2(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;
void f3(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;
void f4(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;

Barrier bn[5]<int state, cl2 x1, cl2 x2, cl2 x3, cl2 x4, cl2 x5> == [
 (1,2,[ requires x1::cl2(@@D1W)<TX1>*x2::cl2(@@D2W)<TX2>*x3::cl2(@@D3W)<TX3>*x4::cl2(@@D4W)<TX4>*x5::cl2<TX5>*self::bn(@@BC)<1,x1,x2,x3,x4,x5> 
			ensures x1::cl2<TX1>*self::bn(@@BC)<2,x1,x2,x3,x4,x5>;,
		requires x1::cl2(@@D1)<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5> ensures x2::cl2<TX2>*self::bn(@@B1)<2,x1,x2,x3,x4,x5>;,
		requires x2::cl2(@@D2)<TX2>*self::bn(@@B2)<1,x1,x2,x3,x4,x5> ensures x3::cl2<TX3>*self::bn(@@B2)<2,x1,x2,x3,x4,x5>;,
		requires x3::cl2(@@D3)<TX3>*self::bn(@@B3)<1,x1,x2,x3,x4,x5> ensures x4::cl2<TX4>*self::bn(@@B3)<2,x1,x2,x3,x4,x5>;,
		requires x4::cl2(@@D4)<TX4>*self::bn(@@B4)<1,x1,x2,x3,x4,x5> ensures x5::cl2<TX5>*self::bn(@@B4)<2,x1,x2,x3,x4,x5>;
		]),
 (2,1,[ requires x1::cl2<TX1>*self::bn(@@BC)<2,x1,x2,x3,x4,x5> 
			ensures x1::cl2(@@D1W)<TX1>*x2::cl2(@@D2W)<TX2>*x3::cl2(@@D3W)<TX3>*x4::cl2(@@D4W)<TX4>*x5::cl2<TX5>*self::bn(@@BC)<1,x1,x2,x3,x4,x5> ;,
		requires x2::cl2<TX2>*self::bn(@@B1)<2,x1,x2,x3,x4,x5> ensures x1::cl2(@@D1)<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5>;,
		requires x3::cl2<TX3>*self::bn(@@B2)<2,x1,x2,x3,x4,x5> ensures x2::cl2(@@D2)<TX2>*self::bn(@@B2)<1,x1,x2,x3,x4,x5>;,
		requires x4::cl2<TX4>*self::bn(@@B3)<2,x1,x2,x3,x4,x5> ensures x3::cl2(@@D3)<TX3>*self::bn(@@B3)<1,x1,x2,x3,x4,x5>;,
		requires x5::cl2<TX5>*self::bn(@@B4)<2,x1,x2,x3,x4,x5> ensures x4::cl2(@@D4)<TX4>*self::bn(@@B4)<1,x1,x2,x3,x4,x5>;
		])];
 
void thl1(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D1)<TX1>*b::bn(@@B1)<1,x1,x2,_,_,_> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f1(a,x2);
	Barrier b;                    // stage 2->1
    thl1 (a,x1,x2, b);
}
 
 void thl2(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D2)<TX1>*b::bn(@@B2)<1,_,x1,x2,_,_> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f2(a,x2);
	Barrier b;                    // stage 2->1
    thl2 (a,x1,x2, b);
}
 
void thl3(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D3)<TX3>*b::bn(@@B3)<1,_,_,x1,x2,_> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f3(a,x2);
	Barrier b;                    // stage 2->1
    thl3 (a,x1,x2, b);
}

void thl4(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D4)<TX4>*b::bn(@@B4)<1,_,_,_,x1,x2> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f4(a,x2);
	Barrier b;                    // stage 2->1
    thl4 (a,x1,x2, b);
}
 
void controll(barrier b)
requires x1::cl2(@@D1W)<TX1>*x2::cl2(@@D2W)<TX2>*x3::cl2(@@D3W)<TX3>*x4::cl2(@@D4W)<TX4>*x5::cl2<TX5>*b::bn(@@BC)<1,x1,x2,x3,x4,x5>
  ensures false;
{
    Barrier b;                    // stage 1->2
    Barrier b;                    // stage 2->1
    controll (b);
}




