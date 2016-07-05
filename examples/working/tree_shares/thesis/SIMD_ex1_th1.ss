
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}

macro C == (#,) 
macro W1 == (,(#,)) 
macro W2 == (,(,#))
macro W12 == (,#)
macro W1C == (#,(#,))
macro W2C == (#,(,#))


Barrier bn[3]<int state, cl i, cl x1, cl p1, cl x2, cl p2, cl x3, cl p3> == [
 (0,1,[ requires i::cl(@@C)<T1>*x1::cl(@@C)<TX1>*p1::cl(@@C)<TP1>*x2::cl(@@C)<TX2>*p2::cl(@@C)<TP2>*x3::cl(@@C)<TX3>*p3::cl(@@C)<TP3>*self::bn(@@C)<0,i,x1,p1,x2,p2,x3,p3> 
			ensures i::cl(@@C)<T1>*x1::cl(@@W2C)<TX1>*p1::cl(@@W2C)<TP1>*x2::cl(@@W1C)<TX2>*p2::cl(@@W1C)<TP2>*x3::cl<TX3>*p3::cl<TP3>*self::bn(@@C)<1,i,x1,p1,x2,p2,x3,p3> ;,
		requires i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*x2::cl(@@W1)<TX2>*p2::cl(@@W1)<TP2>*x3::cl(@@W1)<TX3>*p3::cl(@@W1)<TP3>*self::bn(@@W1)<0,i,x1,p1,x2,p2,x3,p3> 
			ensures i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*self::bn(@@W1)<1,i,x1,p1,x2,p2,x3,p3>;,
		requires i::cl(@@W2)<T1>*x1::cl(@@W2)<TX1>*p1::cl(@@W2)<TP1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*x3::cl(@@W2)<TX3>*p3::cl(@@W2)<TP3>*self::bn(@@W2)<0,i,x1,p1,x2,p2,x3,p3> 
			ensures i::cl(@@W2)<T1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*self::bn(@@W2)<1,i,x1,p1,x2,p2,x3,p3>;
		]),	
 (1,2,[ requires i::cl(@@C)<T1>*x1::cl(@@W2C)<TX1>*p1::cl(@@W2C)<TP1>*x2::cl(@@W1C)<TX2>*p2::cl(@@W1C)<TP2>*x3::cl<TX3>*p3::cl<TP3>*self::bn(@@C)<1,i,x1,p1,x2,p2,x3,p3> & T1<30
			ensures i::cl<T1>*x1::cl<TX1>*p1::cl<TP1>* self::bn(@@C)<2,i,x1,p1,x2,p2,x3,p3> & T1<30 ;,
	requires i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*self::bn(@@W1)<1,i,x1,p1,x2,p2,x3,p3>&T1<30 ensures x2::cl<TX2>*p2::cl<TP2>*self::bn(@@W1)<2,i,x1,p1,x2,p2,x3,p3>;,
	requires i::cl(@@W2)<T1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*self::bn(@@W2)<1,i,x1,p1,x2,p2,x3,p3>&T1<30 ensures x3::cl<TX3>*p3::cl<TP3>*self::bn(@@W2)<2,i,x1,p1,x2,p2,x3,p3>;
		]),
 (2,1,[ requires i::cl<T1>*x1::cl<TX1>*p1::cl<TP1>* self::bn(@@C)<2,i,x1,p1,x2,p2,x3,p3> & T1<30 
		  ensures i::cl(@@C)<T1>*x1::cl(@@W2C)<TX1>*p1::cl(@@W2C)<TP1>*x2::cl(@@W1C)<TX2>*p2::cl(@@W1C)<TP2>*x3::cl<TX3>*p3::cl<TP3>*self::bn(@@C)<1,i,x1,p1,x2,p2,x3,p3> & T1<30;,
		requires x2::cl<TX2>*p2::cl<TP2>*self::bn(@@W1)<2,i,x1,p1,x2,p2,x3,p3> 
		  ensures i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*self::bn(@@W1)<1,i,x1,p1,x2,p2,x3,p3>&T1<30;,
		requires x3::cl<TX3>*p3::cl<TP3>*self::bn(@@W2)<2,i,x1,p1,x2,p2,x3,p3> 
		  ensures i::cl(@@W2)<T1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*self::bn(@@W2)<1,i,x1,p1,x2,p2,x3,p3>&T1<30;
		]) ,
 (1,3,[ requires i::cl(@@C)<T1>*x1::cl(@@W2C)<TX1>*p1::cl(@@W2C)<TP1>*x2::cl(@@W1C)<TX2>*p2::cl(@@W1C)<TP2>*x3::cl<TX3>*p3::cl<TP3>*self::bn(@@C)<1,i,x1,p1,x2,p2,x3,p3> & T1>=30
		  ensures i::cl<T1>*x1::cl<TX1>*p1::cl<TP1>*x2::cl<TX2>*p2::cl<TP2>*x3::cl<TX3>*p3::cl<TP3>*self::bn(@@C)<3,i,x1,p1,x2,p2,x3,p3>& T1>=30;, 
		requires i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*self::bn(@@W1)<1,i,x1,p1,x2,p2,x3,p3>&T1>=30 
			ensures self::bn(@@W1)<3,i,x1,p1,x2,p2,x3,p3>;,
		requires i::cl(@@W2)<T1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*self::bn(@@W2)<1,i,x1,p1,x2,p2,x3,p3>&T1>=30 
			ensures self::bn(@@W2)<3,i,x1,p1,x2,p2,x3,p3>;
		])];

void th1 (cl x1, cl p1, cl x2, cl p2, cl i, barrier b)
	requires i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*x2::cl(@@W1)<TX2>*p2::cl(@@W1)<TP2>*x3::cl(@@W1)<TX3>*p3::cl(@@W1)<TP3>*b::bn(@@W1)<0,i,x1,p1,x2,p2,x3,p3> 
	ensures  b::bn(@@W1)<3,i,x1,p1,x2,p2,x3,p3>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl1 (x1,p1, x2, p2, i, b);
}
 
void thl1(cl x1, cl p1, cl x2, cl p2, cl i,  barrier b)
	requires i::cl(@@W1)<T1>*x1::cl(@@W1)<TX1>*p1::cl(@@W1)<TP1>*b::bn(@@W1)<1,i,x1,p1,x2,p2,x3,p3> ensures b::bn(@@W1)<3,i,x1,p1,x2,p2,x3,p3>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x1.val+ p1.val;
	c = x1.val;
	Barrier b;                    // stage 1->2
	x2.val = c;
	p2.val = t;
    Barrier b;                    // stage 2->1
    thl1 (x1,p1, x2, p2,i, b);
  }
  else Barrier b;                 // stage 1->3
}

void th2 (cl x2, cl p2, cl x3, cl p3, cl i, barrier b)
	requires i::cl(@@W2)<T1>*x1::cl(@@W2)<TX1>*p1::cl(@@W2)<TP1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*x3::cl(@@W2)<TX3>*p3::cl(@@W2)<TP3>*b::bn(@@W2)<0,i,x1,p1,x2,p2,x3,p3> 
	ensures b::bn(@@W2)<3,i,x1,p1,x2,p2,x3,p3>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl2(x2, p2, x3, p3, i, b);
}
 
void thl2(cl x2, cl p2, cl x3, cl p3, cl i,  barrier b)
requires i::cl(@@W2)<T1>*x2::cl(@@W2)<TX2>*p2::cl(@@W2)<TP2>*b::bn(@@W2)<1,i,x1,p1,x2,p2,x3,p3> ensures b::bn(@@W2)<3,i,x1,p1,x2,p2,x3,p3>;
{
  int a1 = 2, t, c ;
  if (i.val<30)
  {                               // stage 1
    t = a1+x2.val + p2.val;
	c = x2.val;
	Barrier b;                    // stage 1->2
	x3.val = c;
	p3.val = t;
    Barrier b;                    // stage 2->1
    thl2(x2,p2, x3, p3, i, b);
  }
  else Barrier b;                 // stage 1->3
}


	
void control (cl i,cl x1, cl p1, barrier b)
requires i::cl(@@C)<T1>*x1::cl(@@C)<TX1>*p1::cl(@@C)<TP1>*x2::cl(@@C)<TX2>*p2::cl(@@C)<TP2>*x3::cl(@@C)<TX3>*p3::cl(@@C)<TP3>*b::bn(@@C)<0,i,x1,p1,x2,p2,x3,p3>  
 ensures i::cl<T1>*x1::cl<TX1>*p1::cl<TP1>*x2::cl<TX2>*p2::cl<TP2>*x3::cl<TX3>*p3::cl<TP3>*b::bn(@@C)<3,i,x1,p1,x2,p2,x3,p3>& T1>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (i,x1,p1,b);
}
 
void controll(cl i, cl x1, cl p1, barrier b)
requires i::cl(@@C)<T1>*x1::cl(@@W2C)<TX1>*p1::cl(@@W2C)<TP1>*x2::cl(@@W1C)<TX2>*p2::cl(@@W1C)<TP2>*x3::cl<TX3>*p3::cl<TP3>*b::bn(@@C)<1,i,x1,p1,x2,p2,x3,p3>
  ensures i::cl<T1>*x1::cl<TX1>*p1::cl<TP1>*x2::cl<TX2>*p2::cl<TP2>*x3::cl<TX3>*p3::cl<TP3>*b::bn(@@C)<3,i,x1,p1,x2,p2,x3,p3>& T1>=30;
{
  if (i.val<30)
  {                               // stage 1
    Barrier b;                    // stage 1->2
    i.val= i.val+1;
	x1.val = i.val;
	p1.val = i.val;
    Barrier b;                    // stage 2->1
    controll (i,x1, p1, b);
  }
  else Barrier b;                 // stage 1->3
}




