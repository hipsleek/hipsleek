
// line
data cl2{int val;}

macro BC == (#,) 
macro B1 == (,(#,)) 
macro B2 == (,(,#))
macro D1 == (#,) 
macro D2 == (,#)

Barrier bn[3]<int state, cl2 x1, cl2 x2, cl2 x3, cl2 x4> == [
 (0,1,[requires x1::cl2(@@BC)<TX1>*x2::cl2(@@BC)<TX2>*x3::cl2(@@BC)<TX3>*x4::cl2(@@BC)<TX4>*self::bn(@@BC)<0,x1,x2,x3,x4> 
		ensures x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4> ;,
	   requires x1::cl2(@@B1)<TX1>*x2::cl2(@@B1)<TX2>*x3::cl2(@@B1)<TX3>*x4::cl2(@@B1)<TX4>*self::bn(@@B1)<0,x1,x2,x3,x4> 
	    ensures x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4> ;,
	   requires x1::cl2(@@B2)<TX1>*x2::cl2(@@B2)<TX2>*x3::cl2(@@B2)<TX3>*x4::cl2(@@B2)<TX4>*self::bn(@@B2)<0,x1,x2,x3,x4> 
		ensures x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4> ;
 ]),
 (1,2,[ requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4> & TX2<30
			ensures x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4> & TX2<30;,
		requires x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4> & TX2<30
			ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4>;,
		requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4> & TX2<30
			ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*self::bn(@@B2)<2,x1,x2,x3,x4>;
		]),
 (2,3,[ requires x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4> & TX1<30
			ensures x1::cl2<TX1>*self::bn(@@BC)<3,x1,x2,x3,x4> ;,
		requires x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4> & TX1<30
			ensures x3::cl2<TX3>*self::bn(@@B1)<3,x1,x2,x3,x4> & TX1<30;,
		requires x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*self::bn(@@B2)<2,x1,x2,x3,x4> & TX1<30
			ensures x2::cl2<TX2>*x4::cl2<TX4>*self::bn(@@B2)<3,x1,x2,x3,x4> ;
 ]),
 (3,2,[ requires x1::cl2<TX1>*self::bn(@@BC)<3,x1,x2,x3,x4> 			ensures x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4> ;,
		requires x3::cl2<TX3>*self::bn(@@B1)<3,x1,x2,x3,x4> 			 ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4> ;,
		requires x2::cl2<TX2>*x4::cl2<TX4>*self::bn(@@B2)<3,x1,x2,x3,x4> ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*self::bn(@@B2)<2,x1,x2,x3,x4> ;
 ]),
 (2,1,[ requires x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4> & TX1>=30 
			ensures x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4> ;,
		requires x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4> & TX1>=30 
			ensures x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4> & TX1>=30;,
		requires x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*self::bn(@@B2)<2,x1,x2,x3,x4>  & TX1>=30
			ensures x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4> ;
		]),
 (1,4,[ requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4> & TX2>=30 ensures x1::cl2<TX1>*self::bn(@@BC)<4,x1,x2,x3,x4> ;,
		requires x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4> & TX2>=30 ensures x2::cl2<TX2>*self::bn(@@B1)<4,x1,x2,x3,x4> & TX2>=30;,
		requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4> & TX2>=30 ensures x3::cl2<TX3>* x4::cl2<TX4>*self::bn(@@B2)<4,x1,x2,x3,x4> ;
 ])];
 
void startert1(cl2 x1, cl2 x2, cl2 x3, cl2 x4,  barrier b)
requires x1::cl2(@@B1)<TX1>*x2::cl2(@@B1)<_>*x3::cl2(@@B1)<TX3>*x4::cl2(@@B1)<TX4>*b::bn(@@B1)<0,x1,x2,x3,x4> 
ensures x2::cl2<TX2>*b::bn(@@B1)<4,x1,x2,x3,x4> & TX2>=30;
{
	Barrier b;
	thl11(x1,x2,x3,x4,b);
}
 
void thl11(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x2::cl2(@@B1)<_>*x1::cl2<TX1>*b::bn(@@B1)<1,x1,x2,x3,x4> ensures x2::cl2<TX2>*b::bn(@@B1)<4,x1,x2,x3,x4> & TX2>=30;
{
	int a,c;
	if (x2.val<30)
	{
		Barrier b;			//1-2
		thl12 (x1,x2,x3,x4, b);
		Barrier b;  //2-1
		thl11(x1,x2,x3,x4,b);
	}
	else Barrier b;
}

void thl12(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x1::cl2(@@B1)<_>*x3::cl2(@@D1)<_>*x4::cl2(@@D1)<_>*b::bn(@@B1)<2,x1,x2,x3,x4> 
	ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<_>*x4::cl2(@@D1)<_>*b::bn(@@B1)<2,x1,x2,x3,x4> & TX1>=30;
{
	int a,c;
		if (x1.val<30)
		{
			a = x3.val;
			c = x4.val;
			Barrier b;	//2-3
			x3.val = a+c;
			Barrier b;	//3-2
			thl12 (x1,x2,x3,x4, b);
		}
}


void startert2(cl2 x1, cl2 x2, cl2 x3, cl2 x4,  barrier b)
requires x1::cl2(@@B2)<TX1>*x2::cl2(@@B2)<_>*x3::cl2(@@B2)<_>*x4::cl2(@@B2)<_>*b::bn(@@B2)<0,x1,x2,x3,x4> 
ensures x3::cl2<TX3>* x4::cl2<TX4>*b::bn(@@B2)<4,x1,x2,x3,x4>;
{
	Barrier b;
	thl21(x1,x2,x3,x4,b);
}
 
void thl21(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*b::bn(@@B2)<1,x1,x2,x3,x4> ensures x3::cl2<TX3>* x4::cl2<TX4>*b::bn(@@B2)<4,x1,x2,x3,x4>;
{
	int a,c;
	if (x2.val<30)
	{
		Barrier b;			//1-2
		thl22 (x1,x2,x3,x4, b);
		Barrier b;  //2-1
		thl21(x1,x2,x3,x4,b);
	}
	else Barrier b;
}

void thl22(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x1::cl2(@@B2)<_>*x3::cl2(@@D2)<_>*x4::cl2(@@D2)<_>*b::bn(@@B2)<2,x1,x2,x3,x4> 
	ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*b::bn(@@B2)<2,x1,x2,x3,x4>  & TX1>=30;
{
	int a,c;
		if (x1.val<30)
		{
			a = x3.val;
			c = x4.val;
			Barrier b;	//2-3
			x4.val = a+c;
			Barrier b;	//3-2
			thl22 (x1,x2,x3,x4, b);
		}
}


void starterc(cl2 x1, cl2 x2,  barrier b)
 requires x1::cl2(@@BC)<TX1>*x2::cl2(@@BC)<TX2>*x3::cl2(@@BC)<TX3>*x4::cl2(@@BC)<TX4>*b::bn(@@BC)<0,x1,x2,x3,x4>  
 ensures b::bn(@@BC)<4,x1,x2,x3,x4>;
{
	Barrier b;
	ctl11(x1,x2,b);
}

void ctl11(cl2 x1, cl2 x2,  barrier b)
 requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*b::bn(@@BC)<1,x1,x2,x3,x4> 
	ensures x1::cl2<TX1>*b::bn(@@BC)<4,x1,x2,x3,x4>;
{
	if (x2.val<30)
	{
		Barrier b;		//1-2
		ctl12(x1,x2,b);
		x2.val = x2.val+1;		
		Barrier b;			//2-1
		ctl11(x1,x2,b);
	}
	else Barrier b;
}

void ctl12(cl2 x1, cl2 x2,  barrier b)
 requires x1::cl2(@@BC)<_>*x2::cl2<_>*b::bn(@@BC)<2,x1,x2,x3,x4>
	ensures x1::cl2(@@BC)<TX1>*x2::cl2<_>*b::bn(@@BC)<2,x1,x2,x3,x4> & TX1>=30;
{
	if (x1.val<30)
		{
			Barrier b;		//2-3
			x1.val = x1.val+1;
			Barrier b;		//3-2
			ctl12 (x1,x2, b);
		}
}
