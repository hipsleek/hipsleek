
// line
data cl2{int val;}

macro BC == (#,) 
macro B1 == (,(#,)) 
macro B2 == (,(,(#,)))
macro B3 == (,(,(,(#,))))
macro B4 == (,(,(,(,#))))
macro D1 == (#,) 
macro D2 == (,#)

Barrier bn[5]<int state, cl2 x1, cl2 x2, cl2 x3, cl2 x4, cl2 x5, cl2 x6> == [
 (0,1,[requires x1::cl2(@@BC)<TX1>*x2::cl2(@@BC)<TX2>*x3::cl2(@@BC)<TX3>*x4::cl2(@@BC)<TX4>*x5::cl2(@@BC)<TX5>*x6::cl2(@@BC)<TX6>*self::bn(@@BC)<0,x1,x2,x3,x4,x5,x6> 
		ensures x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4,x5,x6> ;,
	   requires x1::cl2(@@B1)<TX1>*x2::cl2(@@B1)<TX2>*x3::cl2(@@B1)<TX3>*x4::cl2(@@B1)<TX4>*x5::cl2(@@B1)<TX5>*x6::cl2(@@B1)<TX6>*self::bn(@@B1)<0,x1,x2,x3,x4,x5,x6> 
	    ensures x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5,x6> ;,
	   requires x1::cl2(@@B2)<TX1>*x2::cl2(@@B2)<TX2>*x3::cl2(@@B2)<TX3>*x4::cl2(@@B2)<TX4>*x5::cl2(@@B2)<TX5>*x6::cl2(@@B2)<TX6>*self::bn(@@B2)<0,x1,x2,x3,x4,x5,x6> 
		ensures x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4,x5,x6> ;,
	   requires x1::cl2(@@B3)<TX1>*x2::cl2(@@B3)<TX2>*x3::cl2(@@B3)<TX3>*x4::cl2(@@B3)<TX4>*x5::cl2(@@B3)<TX5>*x6::cl2(@@B3)<TX6>*self::bn(@@B3)<0,x1,x2,x3,x4,x5,x6> 
		ensures x2::cl2(@@B3)<TX2>*x5::cl2<TX5>*self::bn(@@B3)<1,x1,x2,x3,x4,x5,x6> ;,
	   requires x1::cl2(@@B4)<TX1>*x2::cl2(@@B4)<TX2>*x3::cl2(@@B4)<TX3>*x4::cl2(@@B4)<TX4>*x5::cl2(@@B4)<TX5>*x6::cl2(@@B4)<TX6>*self::bn(@@B4)<0,x1,x2,x3,x4,x5,x6> 
		ensures x2::cl2(@@B4)<TX2>*x6::cl2<TX6>*self::bn(@@B4)<1,x1,x2,x3,x4,x5,x6> ;
 ]),
 (1,2,[ requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4,x5,x6> & TX2<30
			ensures x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4,x5,x6> & TX2<30;,
		requires x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5,x6> & TX2<30
			ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4,x5,x6>;,
		requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4,x5,x6> & TX2<30
			ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*x5::cl2(@@D1)<TX5>*self::bn(@@B2)<2,x1,x2,x3,x4,x5,x6>;,
		requires x2::cl2(@@B3)<TX2>*x5::cl2<TX5>*self::bn(@@B3)<1,x1,x2,x3,x4,x5,x6> & TX2<30
			ensures x1::cl2(@@B3)<TX1>*x5::cl2(@@D2)<TX5>*x6::cl2(@@D1)<TX6>*self::bn(@@B3)<2,x1,x2,x3,x4,x5,x6>;,
		requires x2::cl2(@@B4)<TX2>*x6::cl2<TX6>*self::bn(@@B4)<1,x1,x2,x3,x4,x5,x6> & TX2<30
			ensures x1::cl2(@@B4)<TX1>*x6::cl2(@@D2)<TX6>*self::bn(@@B4)<2,x1,x2,x3,x4,x5,x6>;
		]),
 (2,3,[ requires x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4,x5,x6> & TX1<30
			ensures x1::cl2<TX1>*self::bn(@@BC)<3,x1,x2,x3,x4,x5,x6> ;,
		requires x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4,x5,x6> & TX1<30
			ensures x3::cl2<TX3>*self::bn(@@B1)<3,x1,x2,x3,x4,x5,x6> & TX1<30;,
		requires x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*x5::cl2(@@D1)<TX5>*self::bn(@@B2)<2,x1,x2,x3,x4,x5,x6> & TX1<30
			ensures x2::cl2<TX2>*x4::cl2<TX4>*self::bn(@@B2)<3,x1,x2,x3,x4,x5,x6> ;,
		requires x1::cl2(@@B3)<TX1>*x5::cl2(@@D2)<TX5>*x6::cl2(@@D1)<TX6>*self::bn(@@B3)<2,x1,x2,x3,x4,x5,x6> & TX1<30
			ensures x5::cl2<TX5>*self::bn(@@B3)<3,x1,x2,x3,x4,x5,x6> ;,
		requires x1::cl2(@@B4)<TX1>*x6::cl2(@@D2)<TX6>*self::bn(@@B4)<2,x1,x2,x3,x4,x5,x6> & TX1<30
			ensures x6::cl2<TX6>*self::bn(@@B4)<3,x1,x2,x3,x4,x5,x6>;
 ]),
 (3,2,[ requires x1::cl2<TX1>*self::bn(@@BC)<3,x1,x2,x3,x4,x5,x6> 			ensures x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4,x5,x6> ;,
		requires x3::cl2<TX3>*self::bn(@@B1)<3,x1,x2,x3,x4,x5,x6> 			 ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4,x5,x6> ;,
		requires x2::cl2<TX2>*x4::cl2<TX4>*self::bn(@@B2)<3,x1,x2,x3,x4,x5,x6> ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*x5::cl2(@@D1)<TX5>*self::bn(@@B2)<2,x1,x2,x3,x4,x5,x6> ;,
		requires x5::cl2<TX5>*self::bn(@@B3)<3,x1,x2,x3,x4,x5,x6> ensures x1::cl2(@@B3)<TX1>*x5::cl2(@@D2)<TX5>*x6::cl2(@@D1)<TX6>*self::bn(@@B3)<2,x1,x2,x3,x4,x5,x6>  ;,
		requires x6::cl2<TX6>*self::bn(@@B4)<3,x1,x2,x3,x4,x5,x6> ensures x1::cl2(@@B4)<TX1>*x6::cl2(@@D2)<TX6>*self::bn(@@B4)<2,x1,x2,x3,x4,x5,x6> ;
 ]),
 (2,1,[ requires x1::cl2(@@BC)<TX1>*x2::cl2<TX2>*self::bn(@@BC)<2,x1,x2,x3,x4,x5,x6> & TX1>=30 
			ensures x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4,x5,x6> ;,
		requires x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<TX3>*x4::cl2(@@D1)<TX4>*self::bn(@@B1)<2,x1,x2,x3,x4,x5,x6> & TX1>=30 
			ensures x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5,x6> & TX1>=30;,
		requires x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*x5::cl2(@@D1)<TX5>*self::bn(@@B2)<2,x1,x2,x3,x4,x5,x6>  & TX1>=30
			ensures x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4,x5,x6> ;,
		requires x1::cl2(@@B3)<TX1>*x5::cl2(@@D2)<TX5>*x6::cl2(@@D1)<TX6>*self::bn(@@B3)<2,x1,x2,x3,x4,x5,x6> & TX1>=30 
			ensures x2::cl2(@@B3)<TX2>*x5::cl2<TX5>*self::bn(@@B3)<1,x1,x2,x3,x4,x5,x6>;,
		requires x1::cl2(@@B4)<TX1>*x6::cl2(@@D2)<TX6>*self::bn(@@B4)<2,x1,x2,x3,x4,x5,x6> & TX1>=30 
			ensures x2::cl2(@@B4)<TX2>*x6::cl2<TX6>*self::bn(@@B4)<1,x1,x2,x3,x4,x5,x6>;
		]),
 (1,4,[ requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*self::bn(@@BC)<1,x1,x2,x3,x4,x5,x6> & TX2>=30 ensures x1::cl2<TX1>*self::bn(@@BC)<4,x1,x2,x3,x4,x5,x6> ;,
		requires x2::cl2(@@B1)<TX2>*x1::cl2<TX1>*self::bn(@@B1)<1,x1,x2,x3,x4,x5,x6> & TX2>=30 ensures x2::cl2<TX2>*self::bn(@@B1)<4,x1,x2,x3,x4,x5,x6> & TX2>=30;,
		requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*self::bn(@@B2)<1,x1,x2,x3,x4,x5,x6> & TX2>=30 ensures x3::cl2<TX3>* x4::cl2<TX4>*self::bn(@@B2)<4,x1,x2,x3,x4,x5,x6> ;,
		requires x2::cl2(@@B3)<TX2>*x5::cl2<TX5>*self::bn(@@B3)<1,x1,x2,x3,x4,x5,x6> & TX2>=30 ensures x5::cl2<TX5>*self::bn(@@B3)<4,x1,x2,x3,x4,x5,x6> ;,
		requires x2::cl2(@@B4)<TX2>*x6::cl2<TX6>*self::bn(@@B4)<1,x1,x2,x3,x4,x5,x6> & TX2>=30 ensures x6::cl2<TX6>*self::bn(@@B4)<4,x1,x2,x3,x4,x5,x6> ;
 ])];
 
void startert1(cl2 x1, cl2 x2, cl2 x3, cl2 x4,  barrier b)
requires x1::cl2(@@B1)<TX1>*x2::cl2(@@B1)<_>*x3::cl2(@@B1)<TX3>*x4::cl2(@@B1)<TX4>*x5::cl2(@@B1)<_>*x6::cl2(@@B1)<TX6>*b::bn(@@B1)<0,x1,x2,x3,x4,x5,x6> 
ensures x2::cl2<TX2>*b::bn(@@B1)<4,x1,x2,x3,x4,x5,x6> & TX2>=30;
{
	Barrier b;
	thl11(x1,x2,x3,x4,b);
}
 
void thl11(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x2::cl2(@@B1)<_>*x1::cl2<TX1>*b::bn(@@B1)<1,x1,x2,x3,x4,x5,x6> ensures x2::cl2<TX2>*b::bn(@@B1)<4,x1,x2,x3,x4,x5,x6> & TX2>=30;
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
 requires x1::cl2(@@B1)<_>*x3::cl2(@@D1)<_>*x4::cl2(@@D1)<_>*b::bn(@@B1)<2,x1,x2,x3,x4,x5,x6> 
	ensures x1::cl2(@@B1)<TX1>*x3::cl2(@@D1)<_>*x4::cl2(@@D1)<_>*b::bn(@@B1)<2,x1,x2,x3,x4,x5,x6> & TX1>=30;
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
requires x1::cl2(@@B2)<TX1>*x2::cl2(@@B2)<_>*x3::cl2(@@B2)<_>*x4::cl2(@@B2)<_>*x5::cl2(@@B2)<_>*x6::cl2(@@B2)<TX6>*b::bn(@@B2)<0,x1,x2,x3,x4,x5,x6> 
ensures x3::cl2<TX3>* x4::cl2<TX4>*b::bn(@@B2)<4,x1,x2,x3,x4,x5,x6>;
{
	Barrier b;
	thl21(x1,x2,x3,x4,b);
}
 
void thl21(cl2 x1, cl2 x2, cl2 x3,cl2 x4, barrier b)
 requires x2::cl2(@@B2)<TX2>*x3::cl2<TX3>*b::bn(@@B2)<1,x1,x2,x3,x4,x5,x6> ensures x3::cl2<TX3>* x4::cl2<TX4>*b::bn(@@B2)<4,x1,x2,x3,x4,x5,x6>;
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
 requires x1::cl2(@@B2)<_>*x3::cl2(@@D2)<_>*x4::cl2(@@D2)<_>*x5::cl2(@@D1)<_>*b::bn(@@B2)<2,x1,x2,x3,x4,x5,x6> 
	ensures x1::cl2(@@B2)<TX1>*x3::cl2(@@D2)<TX3>*x4::cl2(@@D2)<TX4>*x5::cl2(@@D1)<_>*b::bn(@@B2)<2,x1,x2,x3,x4,x5,x6>  & TX1>=30;
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


void startert3(cl2 x1, cl2 x2, cl2 x5, barrier b)
requires x1::cl2(@@B3)<TX1>*x2::cl2(@@B3)<_>*x3::cl2(@@B3)<_>*x4::cl2(@@B3)<_>*x5::cl2(@@B3)<_>*x6::cl2(@@B3)<_>*b::bn(@@B3)<0,x1,x2,x3,x4,x5,x6> 
ensures x5::cl2<TX5>*b::bn(@@B3)<4,x1,x2,x3,x4,x5,x6>;
{
	Barrier b;
	thl31(x1,x2,x5,b);
}
 
void thl31(cl2 x1, cl2 x2, cl2 x5, barrier b)
 requires x2::cl2(@@B3)<TX2>*x5::cl2<_>*b::bn(@@B3)<1,x1,x2,x3,x4,x5,x6> ensures x5::cl2<_>*b::bn(@@B3)<4,x1,x2,x3,x4,x5,x6>;
{
	int a,c;
	if (x2.val<30)
	{
		Barrier b;			//1-2
		thl32 (x1,x5, b);
		Barrier b;  //2-1
		thl31(x1,x2,x5,b);
	}
	else Barrier b;
}

void thl32(cl2 x1, cl2 x5, barrier b)
 requires x1::cl2(@@B3)<_>*x5::cl2(@@D2)<_>*x6::cl2(@@D1)<_>*b::bn(@@B3)<2,x1,x2,x3,x4,x5,x6>
	ensures x1::cl2(@@B3)<TX1>*x5::cl2(@@D2)<_>*x6::cl2(@@D1)<_>*b::bn(@@B3)<2,x1,x2,x3,x4,x5,x6>  & TX1>=30;
{
	int a,c;
		if (x1.val<30)
		{
			c = x1.val+x5.val;
			Barrier b;	//2-3
			x5.val = a+c;
			Barrier b;	//3-2
			thl32 (x1,x5, b);
		}
}


void startert4(cl2 x1, cl2 x2, cl2 x6, barrier b)
requires x1::cl2(@@B4)<TX1>*x2::cl2(@@B4)<_>*x3::cl2(@@B4)<_>*x4::cl2(@@B4)<_>*x5::cl2(@@B4)<_>*x6::cl2(@@B4)<_>*b::bn(@@B4)<0,x1,x2,x3,x4,x5,x6> 
ensures x6::cl2<_>*b::bn(@@B4)<4,x1,x2,x3,x4,x5,x6>;
{
	Barrier b;
	thl41(x1,x2,x6,b);
}
void thl41(cl2 x1, cl2 x2, cl2 x6, barrier b)
 requires x2::cl2(@@B4)<TX2>*x6::cl2<_>*b::bn(@@B4)<1,x1,x2,x3,x4,x5,x6> ensures x6::cl2<_>*b::bn(@@B4)<4,x1,x2,x3,x4,x5,x6>;
{
	int a,c;
	if (x2.val<30)
	{
		Barrier b;			//1-2
		thl42 (x1,x6, b);
		Barrier b;  //2-1
		thl41(x1,x2,x6,b);
	}
	else Barrier b;
}
void thl42(cl2 x1, cl2 x6, barrier b)
 requires x1::cl2(@@B4)<_>*x6::cl2(@@D2)<_>*b::bn(@@B4)<2,x1,x2,x3,x4,x5,x6>
	ensures x1::cl2(@@B4)<TX1>*x6::cl2(@@D2)<_>*b::bn(@@B4)<2,x1,x2,x3,x4,x5,x6>  & TX1>=30;
{
	int a,c;
		if (x1.val<30)
		{
			c = x1.val+x6.val;
			Barrier b;	//2-3
			x6.val = a+c;
			Barrier b;	//3-2
			thl42 (x1,x6, b);
		}
}
void starterc(cl2 x1, cl2 x2,  barrier b)
 requires x1::cl2(@@BC)<TX1>*x2::cl2(@@BC)<TX2>*x3::cl2(@@BC)<TX3>*x4::cl2(@@BC)<TX4>*x5::cl2(@@BC)<TX5>*x6::cl2(@@BC)<TX6>*b::bn(@@BC)<0,x1,x2,x3,x4,x5,x6>  
 ensures b::bn(@@BC)<4,x1,x2,x3,x4,x5,x6>;
{
	Barrier b;
	ctl11(x1,x2,b);
}

void ctl11(cl2 x1, cl2 x2,  barrier b)
 requires x2::cl2(@@BC)<TX2>*x4::cl2<TX4>*b::bn(@@BC)<1,x1,x2,x3,x4,x5,x6> 
	ensures x1::cl2<TX1>*b::bn(@@BC)<4,x1,x2,x3,x4,x5,x6>;
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
 requires x1::cl2(@@BC)<_>*x2::cl2<_>*b::bn(@@BC)<2,x1,x2,x3,x4,x5,x6>
	ensures x1::cl2(@@BC)<TX1>*x2::cl2<_>*b::bn(@@BC)<2,x1,x2,x3,x4,x5,x6> & TX1>=30;
{
	if (x1.val<30)
		{
			Barrier b;		//2-3
			x1.val = x1.val+1;
			Barrier b;		//3-2
			ctl12 (x1,x2, b);
		}
}
