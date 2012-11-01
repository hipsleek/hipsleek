
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}

macro C == (#,) 
macro W1 == (,(#,)) 
macro W2 == (,(,(#,))) 
macro W3 == (,(,(,(#,))))
macro W4 == (,(,(,(,(#,)))))
macro W5 == (,(,(,(,(,#)))))
macro W12 == (,#)

Barrier bn[6]<int state, cl x, cl y, cl z, cl q, cl w, cl i> == [
 (0,1,[ requires w::cl(@@C )<T6>*q::cl(@@C )<T5>*z::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*i::cl(@@C )<T1>*self::bn(@@C )<0,x,y,z,q,w,i> 
		    ensures w::cl(@@C )<T6>*q::cl(@@C )<T5>*z::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*i::cl(@@C )<T1>*self::bn(@@C )<1,x,y,z,q,w,i>;,
		requires  w::cl(@@W1 )<T6>*q::cl(@@W1 )<T5>*z::cl(@@W1)<T4>*y::cl(@@W1)<T3>*x::cl(@@W1)<T2>*i::cl(@@W1)<T1>*self::bn(@@W1)<0,x,y,z,q,w,i> 
			ensures x::cl(@@W12)<T2>*i::cl(@@W1)<T1>*self::bn(@@W1)<1,x,y,z,q,w,i>;,
		requires w::cl(@@W2 )<T6>*q::cl(@@W2 )<T5>*z::cl(@@W2)<T4>*y::cl(@@W2)<T3>*x::cl(@@W2)<T2>*i::cl(@@W2)<T1>*self::bn(@@W2)<0,x,y,z,q,w,i> 
			ensures y::cl(@@W12)<T3>*i::cl(@@W2)<T1>*self::bn(@@W2)<1,x,y,z,q,w,i>;,
		requires w::cl(@@W3 )<T6>*q::cl(@@W3 )<T5>*z::cl(@@W3)<T4>*y::cl(@@W3)<T3>*x::cl(@@W3)<T2>*i::cl(@@W3)<T1>*self::bn(@@W3)<0,x,y,z,q,w,i> 
			ensures z::cl(@@W12)<T4>*i::cl(@@W3)<T1>*self::bn(@@W3)<1,x,y,z,q,w,i>;,
		requires w::cl(@@W4 )<T6>*q::cl(@@W4 )<T5>*z::cl(@@W4)<T4>*y::cl(@@W4)<T3>*x::cl(@@W4)<T2>*i::cl(@@W4)<T1>*self::bn(@@W4)<0,x,y,z,q,w,i> 
			ensures q::cl(@@W12)<T5>*i::cl(@@W4)<T1>*self::bn(@@W4)<1,x,y,z,q,w,i>;,
		requires w::cl(@@W5 )<T6>*q::cl(@@W5 )<T5>*z::cl(@@W5)<T4>*y::cl(@@W5)<T3>*x::cl(@@W5)<T2>*i::cl(@@W5)<T1>*self::bn(@@W5)<0,x,y,z,q,w,i> 
			ensures w::cl(@@W12)<T6>*i::cl(@@W5)<T1>*self::bn(@@W5)<1,x,y,z,q,w,i>;
		]),	
 (1,2,[ requires w::cl(@@C )<T6>*q::cl(@@C )<T5>*z::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*i::cl(@@C )<T1>*self::bn(@@C )<1,x,y,z,q,w,i> & T1<30 
			ensures i::cl<T >* self::bn(@@C )<2,x,y,z,q,w,i> & T<30 ;,
		requires x::cl(@@W12)<T2>*i::cl(@@W1)<T1>*self::bn(@@W1)<1,x,y,z,q,w,i> & T1<30 ensures x::cl<T2>* self::bn(@@W1)<2,x,y,z,q,w,i>;,
		requires y::cl(@@W12)<T3>*i::cl(@@W2)<T1>*self::bn(@@W2)<1,x,y,z,q,w,i> & T1<30 ensures y::cl<T3>* self::bn(@@W2)<2,x,y,z,q,w,i>;,
		requires z::cl(@@W12)<T4>*i::cl(@@W3)<T1>*self::bn(@@W3)<1,x,y,z,q,w,i> & T1<30 ensures z::cl<T4>* self::bn(@@W3)<2,x,y,z,q,w,i>;,
		requires q::cl(@@W12)<T5>*i::cl(@@W4)<T1>*self::bn(@@W4)<1,x,y,z,q,w,i> & T1<30 ensures q::cl<T5>* self::bn(@@W4)<2,x,y,z,q,w,i>;,
		requires w::cl(@@W12)<T6>*i::cl(@@W5)<T1>*self::bn(@@W5)<1,x,y,z,q,w,i> & T1<30 ensures w::cl<T6>* self::bn(@@W5)<2,x,y,z,q,w,i>;
		]),
 (2,1,[ requires i::cl<T1 >* self::bn(@@C )<2,x,y,z,q,w,i> & T1<30 
			ensures w::cl(@@C )<T6>*q::cl(@@C )<T5>*z::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*i::cl(@@C )<T1>*self::bn(@@C )<1,x,y,z,q,w,i> & T1<30;,
		requires x::cl<T2>* self::bn(@@W1)<2,x,y,z,q,w,i>        ensures x::cl(@@W12)<T2>*i::cl(@@W1)<T1>*self::bn(@@W1)<1,x,y,z,q,w,i> & T1<30;,
		requires y::cl<T3>* self::bn(@@W2)<2,x,y,z,q,w,i>        ensures y::cl(@@W12)<T3>*i::cl(@@W2)<T1>*self::bn(@@W2)<1,x,y,z,q,w,i> & T1<30;,
		requires z::cl<T4>* self::bn(@@W3)<2,x,y,z,q,w,i>        ensures z::cl(@@W12)<T4>*i::cl(@@W3)<T1>*self::bn(@@W3)<1,x,y,z,q,w,i> & T1<30;,
		requires q::cl<T5>* self::bn(@@W4)<2,x,y,z,q,w,i>        ensures q::cl(@@W12)<T5>*i::cl(@@W4)<T1>*self::bn(@@W4)<1,x,y,z,q,w,i> & T1<30;,
		requires w::cl<T6>* self::bn(@@W5)<2,x,y,z,q,w,i>        ensures w::cl(@@W12)<T6>*i::cl(@@W5)<T1>*self::bn(@@W5)<1,x,y,z,q,w,i> & T1<30;
		]) ,
 (1,3,[ requires w::cl(@@C )<T6>*q::cl(@@C )<T5>*z::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*i::cl(@@C)<T1> *self::bn(@@C)<1,x,y,z,q,w,i> & T1>=30 
			ensures i::cl<T>*self::bn(@@C)<3,x,y,z,q,w,i>& T>=30;, 
		requires x::cl(@@W12)<T2>*i::cl(@@W1)<T1> *self::bn(@@W1)<1,x,y,z,q,w,i> & T1>=30 ensures x::cl<T2>*self::bn(@@W1)<3,x,y,z,q,w,i>;,
		requires y::cl(@@W12)<T3>*i::cl(@@W2)<T1> *self::bn(@@W2)<1,x,y,z,q,w,i> & T1>=30 ensures y::cl<T3>*self::bn(@@W2)<3,x,y,z,q,w,i>;,
		requires z::cl(@@W12)<T4>*i::cl(@@W3)<T1> *self::bn(@@W3)<1,x,y,z,q,w,i> & T1>=30 ensures z::cl<T4>*self::bn(@@W3)<3,x,y,z,q,w,i>;,
		requires q::cl(@@W12)<T5>*i::cl(@@W4)<T1> *self::bn(@@W4)<1,x,y,z,q,w,i> & T1>=30 ensures q::cl<T5>*self::bn(@@W4)<3,x,y,z,q,w,i>;,
		requires w::cl(@@W12)<T6>*i::cl(@@W5)<T1> *self::bn(@@W5)<1,x,y,z,q,w,i> & T1>=30 ensures w::cl<T6>*self::bn(@@W5)<3,x,y,z,q,w,i>;
		])];

void th (cl x, cl i, barrier b)
requires w::cl(@@W1)<_>*q::cl(@@W1)<_>*x::cl(@@W1)<_>*y::cl(@@W1)<_>*z::cl(@@W1)<_>*i::cl(@@W1)<_>*b::bn(@@W1)<0,x,y,z,q,w,i> ensures x::cl<_>*b::bn(@@W1)<3,x,y,z,q,w,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl (x,i,b);
}
 
void thl(cl x, cl i, barrier b)
requires x::cl(@@W12)<_>*i::cl(@@W1)<_>*b::bn(@@W1)<1,x,y,z,q,w,i> ensures x::cl<_>*b::bn(@@W1)<3,x,y,z,q,w,i>;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    a = i.val;
    Barrier b;                    // stage 1->2
	x.val = x.val+a;
    Barrier b;                    // stage 2->1
    thl (x,i,b);
  }
  else Barrier b;                 // stage 1->3
}
	

void th2 (cl y, cl i, barrier b)
requires w::cl(@@W2)<_>*q::cl(@@W2)<_>*x::cl(@@W2)<_>*y::cl(@@W2)<_>*z::cl(@@W2)<_>*i::cl(@@W2)<_>*b::bn(@@W2)<0,x,y,z,q,w,i> ensures y::cl<_>*b::bn(@@W2)<3,x,y,z,q,w,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl2 (y,i,b);
}
 
void thl2(cl y, cl i, barrier b)
requires y::cl(@@W12)<_>*i::cl(@@W2)<_>*b::bn(@@W2)<1,x,y,z,q,w,i> ensures y::cl<_>*b::bn(@@W2)<3,x,y,z,q,w,i>;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    a = i.val;
    Barrier b;                    // stage 1->2
	y.val = y.val+a;
    Barrier b;                    // stage 2->1
    thl2 (y,i,b);
  }
  else Barrier b;                 // stage 1->3
}

void th3 (cl z, cl i, barrier b)
requires w::cl(@@W3)<_>*q::cl(@@W3)<_>*x::cl(@@W3)<_>*y::cl(@@W3)<_>*z::cl(@@W3)<_>*i::cl(@@W3)<_>*b::bn(@@W3)<0,x,y,z,q,w,i> ensures z::cl<_>*b::bn(@@W3)<3,x,y,z,q,w,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl3 (z,i,b);
}
 
void thl3(cl z, cl i, barrier b)
requires z::cl(@@W12)<_>*i::cl(@@W3)<_>*b::bn(@@W3)<1,x,y,z,q,w,i> ensures z::cl<_>*b::bn(@@W3)<3,x,y,z,q,w,i>;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    a = i.val;
    Barrier b;                    // stage 1->2
	z.val = z.val+a;
    Barrier b;                    // stage 2->1
    thl3 (z,i,b);
  }
  else Barrier b;                 // stage 1->3
}		
	
void th4 (cl q, cl i, barrier b)
requires w::cl(@@W4)<_>*q::cl(@@W4)<_>*x::cl(@@W4)<_>*y::cl(@@W4)<_>*z::cl(@@W4)<_>*i::cl(@@W4)<_>*b::bn(@@W4)<0,x,y,z,q,w,i> ensures q::cl<_>*b::bn(@@W4)<3,x,y,z,q,w,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl4 (q,i,b);
}

void thl4(cl q, cl i, barrier b)
requires q::cl(@@W12)<_>*i::cl(@@W4)<_>*b::bn(@@W4)<1,x,y,z,q,w,i> ensures q::cl<_>*b::bn(@@W4)<3,x,y,z,q,w,i>;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    a = i.val;
    Barrier b;                    // stage 1->2
	q.val = q.val+a;
    Barrier b;                    // stage 2->1
    thl4 (q,i,b);
  }
  else Barrier b;                 // stage 1->3
} 	

	
void th5 (cl w, cl i, barrier b)
requires w::cl(@@W5)<_>*q::cl(@@W5)<_>*x::cl(@@W5)<_>*y::cl(@@W5)<_>*z::cl(@@W5)<_>*i::cl(@@W5)<_>*b::bn(@@W5)<0,x,y,z,q,w,i> 
	ensures w::cl<_>*b::bn(@@W5)<3,x,y,z,q,w,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl5 (w,i,b);
}

void thl5(cl w, cl i, barrier b)
requires w::cl(@@W12)<_>*i::cl(@@W5)<_>*b::bn(@@W5)<1,x,y,z,q,w,i> ensures w::cl<_>*b::bn(@@W5)<3,x,y,z,q,w,i>;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    a = i.val;
    Barrier b;                    // stage 1->2
	w.val = w.val+a;
    Barrier b;                    // stage 2->1
    thl5 (w,i,b);
  }
  else Barrier b;                 // stage 1->3
} 

void control (cl x, cl y, cl z, cl q, cl w, cl i, barrier b)
requires w::cl(@@C )<T5>*q::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*z::cl(@@C)<_>*i::cl(@@C)<_>*b::bn(@@C)<0,x,y,z,q,w,i> 
 ensures i::cl<a>*b::bn(@@C)<3,x,y,z,q,w,i> & a>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (x,y,z,q,w,i,b);
}
 
void controll(cl x, cl y, cl z, cl q, cl w, cl i, barrier b)
requires  w::cl(@@C )<T5>*q::cl(@@C )<T4>*y::cl(@@C )<T3>*x::cl(@@C )<T2>*z::cl(@@C)<_>*i::cl(@@C)<_>*b::bn(@@C)<1,x,y,z,q,w,i> 
  ensures i::cl<a>*b::bn(@@C)<3,x,y,z,q,w,i> & a>=30;
{
  int a;
  if (i.val<30)
  {                               // stage 1
    Barrier b;                    // stage 1->2
    i.val= i.val+1;
    Barrier b;                    // stage 2->1
	a= x.val+y.val+z.val+q.val;
    controll (x,y,z,q,w,i,b);
  }
  else Barrier b;                 // stage 1->3
}
