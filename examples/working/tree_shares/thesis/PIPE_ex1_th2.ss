
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}
data cl2{int x;}

macro BC == (#,) 
macro B1 == (,(#,)) 
macro B2 == (,(,#))
macro D1 == (#,) 
macro D2 == (,#)


void f1(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;
void f2(cl2 x, cl2 y) requires x::cl2(v1)<a>*y::cl2<_> ensures x::cl2(v1)<a>*y::cl2<_>;

Barrier bn[3]<int state, cl2 x1, cl2 x2, cl2 x3> == [
 (1,2,[ requires x1::cl2(@@D2)<TX1>*x2::cl2(@@D1)<TX2>*x3::cl2<TX3>*self::bn(@@BC)<1,x1,x2,x3> ensures x1::cl2<TX1>*self::bn(@@BC)<2,x1,x2,x3>;,
		requires x1::cl2(@@D1)<TX1>*self::bn(@@B1)<1,x1,x2,x3> ensures x2::cl2<TX2>*self::bn(@@B1)<2,x1,x2,x3>;,
		requires x2::cl2(@@D2)<TX2>*self::bn(@@B2)<1,x1,x2,x3> ensures x3::cl2<TX3>*self::bn(@@B2)<2,x1,x2,x3>;
		]),
 (2,1,[ requires x1::cl2<TX1>*self::bn(@@BC)<2,x1,x2,x3> ensures x1::cl2(@@D2)<TX1>*x2::cl2(@@D1)<TX2>*x3::cl2<TX3>*self::bn(@@BC)<1,x1,x2,x3>;,
		requires x2::cl2<TX2>*self::bn(@@B1)<2,x1,x2,x3> ensures x1::cl2(@@D1)<TX1>*self::bn(@@B1)<1,x1,x2,x3>;,
		requires x3::cl2<TX3>*self::bn(@@B2)<2,x1,x2,x3> ensures x2::cl2(@@D2)<TX2>*self::bn(@@B2)<1,x1,x2,x3>;
		])];
 
void thl1(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D1)<TX1>*b::bn(@@B1)<1,x1,x2,x3> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f1(a,x2);
	Barrier b;                    // stage 2->1
    thl1 (a,x1,x2, b);
}
 
 void thl2(cl2 a, cl2 x1, cl2 x2,  barrier b)
	requires a::cl2<_>*x1::cl2(@@D2)<TX1>*b::bn(@@B2)<1,_,x1,x2> ensures false;
{
	a.x = x1.x;
	Barrier b;                    // stage 1->2
	f2(a,x2);
	Barrier b;                    // stage 2->1
    thl2 (a,x1,x2, b);
}
 
void controll(barrier b)
requires x1::cl2(@@D2)<TX1>*x2::cl2(@@D1)<TX2>*x3::cl2<TX3>*b::bn(@@BC)<1,x1,x2,x3>
  ensures false;
{
    Barrier b;                    // stage 1->2
    Barrier b;                    // stage 2->1
    controll (b);
}




