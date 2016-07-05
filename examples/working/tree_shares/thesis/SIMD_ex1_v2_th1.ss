
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}
data cl2{int x; int p;}

macro C == (#,) 
macro W1 == (,(#,)) 
macro W2 == (,(,#))
macro W12 == (,#)
macro W1C == (#,(#,))
macro W2C == (#,(,#))


Barrier bn[3]<int state, cl i, cl2 x1, cl2 x2, cl2 x3> == [
 (0,1,[ requires i::cl(@@C)<T1>*x1::cl2(@@C)<TX1,TP1>*x2::cl2(@@C)<TX2,TP2>*x3::cl2(@@C)<TX3,TP3>*self::bn(@@C)<0,i,x1,x2,x3> 
			ensures i::cl(@@C)<T1>*x1::cl2(@@W2C)<TX1,TP1>*x2::cl2(@@W1C)<TX2,TP2>*x3::cl2<TX3,TP3>*self::bn(@@C)<1,i,x1,x2,x3> ;,
		requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*x2::cl2(@@W1)<TX2,TP2>*x3::cl2(@@W1)<TX3,TP3>*self::bn(@@W1)<0,i,x1,x2,x3> 
			ensures i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3>;,
		requires i::cl(@@W2)<T1>*x1::cl2(@@W2)<TX1,TP1>*x2::cl2(@@W2)<TX2,TP2>*x3::cl2(@@W2)<TX3,TP3>*self::bn(@@W2)<0,i,x1,x2,x3> 
			ensures i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3>;
		]),	
 (1,2,[ requires i::cl(@@C)<T1>*x1::cl2(@@W2C)<TX1,TP1>*x2::cl2(@@W1C)<TX2,TP2>*x3::cl2<TX3,TP3>*self::bn(@@C)<1,i,x1,x2,x3> & T1<30
			ensures i::cl<T1>*x1::cl2<TX1,TP1>* self::bn(@@C)<2,i,x1,x2,x3> & T1<30 ;,
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3>&T1<30 ensures x2::cl2<TX2,TP2>*self::bn(@@W1)<2,i,x1,x2,x3>;,
	requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3>&T1<30 ensures x3::cl2<TX3,TP3>*self::bn(@@W2)<2,i,x1,x2,x3>;
		]),
 (2,1,[ requires i::cl<T1>*x1::cl2<TX1,TP1>*self::bn(@@C)<2,i,x1,x2,x3> & T1<30 
		  ensures i::cl(@@C)<T1>*x1::cl2(@@W2C)<TX1,TP1>*x2::cl2(@@W1C)<TX2,TP2>*x3::cl2<TX3,TP3>*self::bn(@@C)<1,i,x1,x2,x3> & T1<30;,
		requires x2::cl2<TX2,TP2>*self::bn(@@W1)<2,i,x1,x2,x3> ensures i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3>&T1<30;,
		requires x3::cl2<TX3,TP3>*self::bn(@@W2)<2,i,x1,x2,x3> ensures i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3>&T1<30;
		]) ,
 (1,3,[ requires i::cl(@@C)<T1>*x1::cl2(@@W2C)<TX1,TP1>*x2::cl2(@@W1C)<TX2,TP2>*x3::cl2<TX3,TP3>*self::bn(@@C)<1,i,x1,x2,x3> & T1>=30
		  ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*self::bn(@@C)<3,i,x1,x2,x3>& T1>=30;, 
		requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*self::bn(@@W1)<1,i,x1,x2,x3>&T1>=30 ensures self::bn(@@W1)<3,i,x1,x2,x3>;,
		requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*self::bn(@@W2)<1,i,x1,x2,x3>&T1>=30 ensures self::bn(@@W2)<3,i,x1,x2,x3>;
		])];

void th1 (cl2 x1, cl2 x2, cl i, barrier b)
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*x2::cl2(@@W1)<TX2,TP2>*x3::cl2(@@W1)<TX3,TP3>*b::bn(@@W1)<0,i,x1,x2,x3> ensures  b::bn(@@W1)<3,i,x1,x2,x3>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl1 (x1, x2, i, b);
}
 
void thl1(cl2 x1, cl2 x2, cl i,  barrier b)
	requires i::cl(@@W1)<T1>*x1::cl2(@@W1)<TX1,TP1>*b::bn(@@W1)<1,i,x1,x2,x3> ensures b::bn(@@W1)<3,i,x1,x2,x3>;
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
	requires i::cl(@@W2)<T1>*x1::cl2(@@W2)<TX1,TP1>*x2::cl2(@@W2)<TX2,TP2>*x3::cl2(@@W2)<TX3,TP3>*b::bn(@@W2)<0,i,x1,x2,x3> ensures b::bn(@@W2)<3,i,x1,x2,x3>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl2(x2, x3, i, b);
}
 
void thl2(cl2 x2, cl2 x3, cl i,  barrier b)
requires i::cl(@@W2)<T1>*x2::cl2(@@W2)<TX2,TP2>*b::bn(@@W2)<1,i,x1,x2,x3> ensures b::bn(@@W2)<3,i,x1,x2,x3>;
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


	
void control (cl i,cl2 x1, barrier b)
requires i::cl(@@C)<T1>*x1::cl2(@@C)<TX1,TP1>*x2::cl2(@@C)<TX2,TP2>*x3::cl2(@@C)<TX3,TP3>*b::bn(@@C)<0,i,x1,x2,x3>  
 ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*b::bn(@@C)<3,i,x1,x2,x3>& T1>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (i,x1,b);
}
 
void controll(cl i, cl2 x1, barrier b)
requires i::cl(@@C)<T1>*x1::cl2(@@W2C)<TX1,TP1>*x2::cl2(@@W1C)<TX2,TP2>*x3::cl2<TX3,TP3>*b::bn(@@C)<1,i,x1,x2,x3>
  ensures i::cl<T1>*x1::cl2<TX1,TP1>*x2::cl2<TX2,TP2>*x3::cl2<TX3,TP3>*b::bn(@@C)<3,i,x1,x2,x3>& T1>=30;
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




