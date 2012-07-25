
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}
data cl2{int x; int p;}

macro C == (#,) 
macro W1 == (,(#,)) 
macro W2 == (,(,(#,)))
macro W3 == (,(,(,(#,))))
macro W4 == (,(,(,(,#))))
macro W1C == (#,(,#))
macro W2C == (#,(#,(,#)))
macro W3C == (#,(#,(#,(,#))))
macro W4C == (#,(#,(#,(#,))))


Barrier bn[5]<int state, cl i, cl2 x1, cl2 x2, cl2 x3, cl2 x4, cl2 x5> == [
 (0,1,[requires i::cl(@@C)<T1>*x1::cl2(@@C)<TX1,TP1>*x2::cl2(@@C)<TX2,TP2>*x3::cl2(@@C)<TX3,TP3>*x4::cl2(@@C)<TX4,TP4>*x5::cl2(@@C)<TX5,TP5>*self::bn(@@C)<0,i,x1,x2,x3,x4,x5> 
		 ensures i::cl(@@C)<T1>*x1::cl2(@@W1C)<TX1,TP1>*x2::cl2(@@W2C)<TX2,TP2>*x3::cl2(@@W3C)<TX3,TP3>*x4::cl2(@@W4C)<TX4,TP4>*x5::cl2<TX5,TP5>*self::bn(@@C)<1,i,x1,x2,x3,x4,x5> ;,
	   requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*x2::cl2(@@W1)<TX2,TP2>*x3::cl2(@@W1)<TX3,TP3>*x4::cl2(@@W1)<TX4,TP4>*x5::cl2(@@W1)<TX5,TP5>*self::bn(@@W1)<0,i,x1,x2,x3,x4,x5> 
			ensures i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3,x4,x5>;,
	   requires i::cl(@@W2)<T1>*x1::cl2(@@W2)<TX1,TP1>*x2::cl2(@@W2)<TX2,TP2>*x3::cl2(@@W2)<TX3,TP3>*x4::cl2(@@W2)<TX4,TP4>*x5::cl2(@@W2)<TX5,TP5>*self::bn(@@W2)<0,i,x1,x2,x3,x4,x5> 
			ensures i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3,x4,x5>;,
	   requires i::cl(@@W3)<T1>*x1::cl2(@@W3)<TX1,TP1>*x2::cl2(@@W3)<TX2,TP2>*x3::cl2(@@W3)<TX3,TP3>*x4::cl2(@@W3)<TX4,TP4>*x5::cl2(@@W3)<TX5,TP5>*self::bn(@@W3)<0,i,x1,x2,x3,x4,x5> 
			ensures i::cl(@@W3)<T1>*x3::cl2(@@W3)<TX3,TP3>*self::bn(@@W3)<1,i,x1,x2,x3,x4,x5>;,
	   requires i::cl(@@W4)<T1>*x1::cl2(@@W4)<TX1,TP1>*x2::cl2(@@W4)<TX2,TP2>*x3::cl2(@@W4)<TX3,TP3>*x4::cl2(@@W4)<TX4,TP4>*x5::cl2(@@W4)<TX5,TP5>*self::bn(@@W4)<0,i,x1,x2,x3,x4,x5> 
			ensures i::cl(@@W4)<T1>*x4::cl2(@@W4)<TX4,TP4>*self::bn(@@W4)<1,i,x1,x2,x3,x4,x5>;
		]),	
 (1,2,[ requires i::cl(@@C)<T1>*x1::cl2(@@W1C)<TX1,TP1>*x2::cl2(@@W2C)<TX2,TP2>*x3::cl2(@@W3C)<TX3,TP3>*x4::cl2(@@W4C)<TX4,TP4>*x5::cl2<TX5,TP5>*self::bn(@@C)<1,i,x1,x2,x3,x4,x5> & T1<30
			ensures i::cl<T1>*x1::cl2<TX1,TP1>* self::bn(@@C)<2,i,x1,x2,x3,x4,x5> & T1<30 ;,
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3,x4,x5>&T1<30 ensures x2::cl2<TX2,TP2>*self::bn(@@W1)<2,i,x1,x2,x3,x4,x5>;,
	requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3,x4,x5>&T1<30 ensures x3::cl2<TX3,TP3>*self::bn(@@W2)<2,i,x1,x2,x3,x4,x5>;,
	requires i::cl(@@W3)<T1>*x3::cl2(@@W3)<TX3,TP3>*self::bn(@@W3)<1,i,x1,x2,x3,x4,x5>&T1<30 ensures x4::cl2<TX4,TP4>*self::bn(@@W3)<2,i,x1,x2,x3,x4,x5>;,
	requires i::cl(@@W4)<T1>*x4::cl2(@@W4)<TX4,TP4>*self::bn(@@W4)<1,i,x1,x2,x3,x4,x5>&T1<30 ensures x5::cl2<TX5,TP5>*self::bn(@@W4)<2,i,x1,x2,x3,x4,x5>;
		]),
 (2,1,[ requires i::cl<T1>*x1::cl2<TX1,TP1>*self::bn(@@C)<2,i,x1,x2,x3,x4,x5> & T1<30 
		  ensures i::cl(@@C)<T1>*x1::cl2(@@W1C)<TX1,TP1>*x2::cl2(@@W2C)<TX2,TP2>*x3::cl2(@@W3C)<TX3,TP3>*x4::cl2(@@W4C)<TX4,TP4>*x5::cl2<TX5,TP5>*self::bn(@@C)<1,i,x1,x2,x3,x4,x5> & T1<30;,
		requires x2::cl2<TX2,TP2>*self::bn(@@W1)<2,i,x1,x2,x3,x4,x5> ensures i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3,x4,x5>&T1<30;,
		requires x3::cl2<TX3,TP3>*self::bn(@@W2)<2,i,x1,x2,x3,x4,x5> ensures i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3,x4,x5>&T1<30;,
		requires x4::cl2<TX4,TP4>*self::bn(@@W3)<2,i,x1,x2,x3,x4,x5> ensures i::cl(@@W3)<T1>*x3::cl2(@@W3)<TX3,TP3>*self::bn(@@W3)<1,i,x1,x2,x3,x4,x5>&T1<30;,
		requires x5::cl2<TX5,TP5>*self::bn(@@W4)<2,i,x1,x2,x3,x4,x5> ensures i::cl(@@W4)<T1>*x4::cl2(@@W4)<TX4,TP4>*self::bn(@@W4)<1,i,x1,x2,x3,x4,x5>&T1<30;
		]) ,
 (1,3,[ requires i::cl(@@C)<T1>*x1::cl2(@@W1C)<TX1,TP1>*x2::cl2(@@W2C)<TX2,TP2>*x3::cl2(@@W3C)<TX3,TP3>*x4::cl2(@@W4C)<TX4,TP4>*x5::cl2<TX5,TP5>*self::bn(@@C)<1,i,x1,x2,x3,x4,x5> & T1>=30
		  ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*x4::cl2<TX4,TP4>*x5::cl2<TX5,TP5>*self::bn(@@C)<3,i,x1,x2,x3,x4,x5>& T1>=30;, 
		requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3,x4,x5>&T1>=30 ensures self::bn(@@W1)<3,i,x1,x2,x3,x4,x5>;,
		requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3,x4,x5>&T1>=30 ensures self::bn(@@W2)<3,i,x1,x2,x3,x4,x5>;,
		requires i::cl(@@W3)<T1>*x3::cl2(@@W3)<TX3,TP3>*self::bn(@@W3)<1,i,x1,x2,x3,x4,x5>&T1>=30 ensures self::bn(@@W3)<3,i,x1,x2,x3,x4,x5>;,
		requires i::cl(@@W4)<T1>*x4::cl2(@@W4)<TX4,TP4>*self::bn(@@W4)<1,i,x1,x2,x3,x4,x5>&T1>=30 ensures self::bn(@@W4)<3,i,x1,x2,x3,x4,x5>;
		])];

void th1 (cl2 x1, cl2 x2, cl i, barrier b)
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*x2::cl2(@@W1)<TX2,TP2>*x3::cl2(@@W1)<TX3,TP3>*x4::cl2(@@W1)<TX4,TP4>*x5::cl2(@@W1)<TX5,TP5>*b::bn(@@W1)<0,i,x1,x2,x3,x4,x5> 
	ensures  b::bn(@@W1)<3,i,x1,x2,x3,x4,x5>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl1 (x1, x2, i, b);
}
 
void thl1(cl2 x1, cl2 x2, cl i,  barrier b)
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*b::bn(@@W1)<1,i,x1,x2,x3,x4,x5> ensures b::bn(@@W1)<3,i,x1,x2,x3,x4,x5>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x1.x+ x1.p;
	c = x1.x;
	Barrier b;                    // stage 1->2
	x2.x = c;
	x2.p = t;
    Barrier b;                    // stage 2->1
    thl1 (x1,x2,i, b);
  }
  else Barrier b;                 // stage 1->3
}

void th2 (cl2 x2, cl2 x3, cl i, barrier b)
	requires i::cl(@@W2)<T1>*x1::cl2(@@W2)<TX1,TP1>*x2::cl2(@@W2)<TX2,TP2>*x3::cl2(@@W2)<TX3,TP3>*x4::cl2(@@W2)<TX4,TP4>*x5::cl2(@@W2)<TX5,TP5>*b::bn(@@W2)<0,i,x1,x2,x3,x4,x5> 
	ensures b::bn(@@W2)<3,i,x1,x2,x3,x4,x5>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl2(x2, x3, i, b);
}
 
void thl2(cl2 x2, cl2 x3, cl i,  barrier b)
requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*b::bn(@@W2)<1,i,x1,x2,x3,x4,x5> ensures b::bn(@@W2)<3,i,x1,x2,x3,x4,x5>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x2.x + x2.p;
	c = x2.x;
	Barrier b;                    // stage 1->2
	x3.x = c;
	x3.p = t;
    Barrier b;                    // stage 2->1
    thl2(x2, x3, i, b);
  }
  else Barrier b;                 // stage 1->3
}


void th3 (cl2 x3, cl2 x4, cl i, barrier b)
	requires i::cl(@@W3)<T1>*x1::cl2(@@W3)<TX1,TP1>*x2::cl2(@@W3)<TX2,TP2>*x3::cl2(@@W3)<TX3,TP3>*x4::cl2(@@W3)<TX4,TP4>*x5::cl2(@@W3)<TX5,TP5>*b::bn(@@W3)<0,i,x1,x2,x3,x4,x5> 
	ensures b::bn(@@W3)<3,i,x1,x2,x3,x4,x5>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl3(x3, x4, i, b);
}
 
void thl3(cl2 x3, cl2 x4, cl i,  barrier b)
requires i::cl(@@W3)<T1>*x3::cl2(@@W3)<TX3,TP3>*b::bn(@@W3)<1,i,x1,x2,x3,x4,x5> ensures b::bn(@@W3)<3,i,x1,x2,x3,x4,x5>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x3.x + x3.p;
	c = x3.x;
	Barrier b;                    // stage 1->2
	x4.x = c;
	x4.p = t;
    Barrier b;                    // stage 2->1
    thl3(x3, x4, i, b);
  }
  else Barrier b;                 // stage 1->3
}
	
void th4 (cl2 x4, cl2 x5, cl i, barrier b)
	requires i::cl(@@W4)<T1>*x1::cl2(@@W4)<TX1,TP1>*x2::cl2(@@W4)<TX2,TP2>*x3::cl2(@@W4)<TX3,TP3>*x4::cl2(@@W4)<TX4,TP4>*x5::cl2(@@W4)<TX5,TP5>*b::bn(@@W4)<0,i,x1,x2,x3,x4,x5> 
	ensures b::bn(@@W4)<3,i,x1,x2,x3,x4,x5>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl4(x4, x5, i, b);
}
 
void thl4(cl2 x4, cl2 x5, cl i,  barrier b)
requires i::cl(@@W4)<T1>*x4::cl2(@@W4)<TX3,TP3>*b::bn(@@W4)<1,i,x1,x2,x3,x4,x5> ensures b::bn(@@W4)<3,i,x1,x2,x3,x4,x5>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x4.x + x4.p;
	c = x4.x;
	Barrier b;                    // stage 1->2
	x5.x = c;
	x5.p = t;
    Barrier b;                    // stage 2->1
    thl4(x4, x5, i, b);
  }
  else Barrier b;                 // stage 1->3
}

	
void control (cl i,cl2 x1, barrier b)
requires i::cl(@@C)<T1>*x1::cl2(@@C)<TX1,TP1>*x2::cl2(@@C)<TX2,TP2>*x3::cl2(@@C)<TX3,TP3>*x4::cl2(@@C)<TX4,TP4>*x5::cl2(@@C)<TX5,TP5>*b::bn(@@C)<0,i,x1,x2,x3,x4,x5>  
 ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*x4::cl2<TX4,TP4>*x5::cl2<TX5,TP5>*b::bn(@@C)<3,i,x1,x2,x3,x4,x5>& T1>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (i,x1,b);
}
 
void controll(cl i, cl2 x1, barrier b)
requires i::cl(@@C)<T1>*x1::cl2(@@W1C)<TX1,TP1>*x2::cl2(@@W2C)<TX2,TP2>*x3::cl2(@@W3C)<TX3,TP3>*x4::cl2(@@W4C)<TX4,TP4>*x5::cl2<TX5,TP5>*b::bn(@@C)<1,i,x1,x2,x3,x4,x5>
  ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*x4::cl2<TX4,TP4>*x5::cl2<TX5,TP5>*b::bn(@@C)<3,i,x1,x2,x3,x4,x5>& T1>=30;
  {
  if (i.val<30)
  {                               // stage 1
    Barrier b;                    // stage 1->2
    i.val= i.val+1;
	x1.x = i.val;
	x1.p = i.val;
    Barrier b;                    // stage 2->1
    controll (i,x1,b);
  }
  else Barrier b;                 // stage 1->3
}




