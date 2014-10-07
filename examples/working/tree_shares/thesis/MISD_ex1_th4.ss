
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}

macro C == (#,) 
macro W1 == (,(#,)) 
macro W2 == (,(,(#,))) 
macro W3 == (,(,(,(#,))))
macro W4 == (,(,(,(,#)))) 

Barrier bn[5]<int state, cl i> == [
 (0,1,[ requires i::cl(@@C)<T1>*self::bn(@@C)<0,i> ensures i::cl(@@C)<T1>*self::bn(@@C)<1,i> ;,
		requires i::cl(@@W1)<T2>*self::bn(@@W1)<0,i> ensures i::cl(@@W1)<T2>*self::bn(@@W1)<1,i>;,
		requires i::cl(@@W2)<T2>*self::bn(@@W2)<0,i> ensures i::cl(@@W2)<T2>*self::bn(@@W2)<1,i>;,
		requires i::cl(@@W3)<T2>*self::bn(@@W3)<0,i> ensures i::cl(@@W3)<T2>*self::bn(@@W3)<1,i>;,
		requires i::cl(@@W4)<T2>*self::bn(@@W4)<0,i> ensures i::cl(@@W4)<T2>*self::bn(@@W4)<1,i>;
		]),	
 (1,2,[ requires i::cl(@@C)<T> *self::bn(@@C)<1,i> & T<30  ensures i::cl<T>* self::bn(@@C)<2,i> & T<30 ;,
		requires i::cl(@@W1)<T> *self::bn(@@W1)<1,i> & T<30  ensures 			self::bn(@@W1)<2,i>;,
		requires i::cl(@@W2)<T> *self::bn(@@W2)<1,i> & T<30  ensures 			self::bn(@@W2)<2,i>;,
		requires i::cl(@@W3)<T> *self::bn(@@W3)<1,i> & T<30  ensures 			self::bn(@@W3)<2,i>;,
		requires i::cl(@@W4)<T> *self::bn(@@W4)<1,i> & T<30  ensures 			self::bn(@@W4)<2,i>;
		]),
 (2,1,[ requires i::cl<T>*self::bn(@@C)<2,i>  		   ensures i::cl(@@C)<T>*self::bn(@@C)<1,i>;,
		requires 	      self::bn(@@W1)<2,i>		   ensures i::cl(@@W1)<T>*self::bn(@@W1)<1,i>;,
		requires 	      self::bn(@@W2)<2,i>		   ensures i::cl(@@W2)<T>*self::bn(@@W2)<1,i>;,
		requires 	      self::bn(@@W3)<2,i>		   ensures i::cl(@@W3)<T>*self::bn(@@W3)<1,i>;,
		requires 	      self::bn(@@W4)<2,i>		   ensures i::cl(@@W4)<T>*self::bn(@@W4)<1,i>;
		]) ,
 (1,3,[ requires i::cl(@@C)<T> *self::bn(@@C)<1,i> & T>=30 ensures i::cl<T>*self::bn(@@C)<3,i>& T>=30;, 
		requires i::cl(@@W1)<T> *self::bn(@@W1)<1,i> & T>=30 ensures self::bn(@@W1)<3,i>;,
		requires i::cl(@@W2)<T> *self::bn(@@W2)<1,i> & T>=30 ensures self::bn(@@W2)<3,i>;,
		requires i::cl(@@W3)<T> *self::bn(@@W3)<1,i> & T>=30 ensures self::bn(@@W3)<3,i>;,
		requires i::cl(@@W4)<T> *self::bn(@@W4)<1,i> & T>=30 ensures self::bn(@@W4)<3,i>;
		])];

void th (cl i, barrier b)
requires i::cl(@@W1)<_>*b::bn(@@W1)<0,i>  ensures b::bn(@@W1)<3,i>;
requires i::cl(@@W2)<_>*b::bn(@@W2)<0,i>  ensures b::bn(@@W2)<3,i>;
requires i::cl(@@W3)<_>*b::bn(@@W3)<0,i>  ensures b::bn(@@W3)<3,i>;
requires i::cl(@@W4)<_>*b::bn(@@W4)<0,i>  ensures b::bn(@@W4)<3,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl (i,b);
}
 
void thl(cl i, barrier b)
requires i::cl(@@W1)<_>*b::bn(@@W1)<1,i> ensures b::bn(@@W1)<3,i>;
requires i::cl(@@W2)<_>*b::bn(@@W2)<1,i> ensures b::bn(@@W2)<3,i>;
requires i::cl(@@W3)<_>*b::bn(@@W3)<1,i> ensures b::bn(@@W3)<3,i>;
requires i::cl(@@W4)<_>*b::bn(@@W4)<1,i> ensures b::bn(@@W4)<3,i>;
{
  int x ;
  if (i.val<30)
  {                               // stage 1
    x = x+i.val;
    Barrier b;                    // stage 1->2
    Barrier b;                    // stage 2->1
    thl (i,b);
  }
  else Barrier b;                 // stage 1->3
}
	
void control (cl i, barrier b)
requires i::cl(@@C)<1>*b::bn(@@C)<0,i> 
 ensures i::cl(@@C)<a>*b::bn(@@C)<3,i> & a>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (i,b);
}
 
void controll(cl i, barrier b)
requires i::cl(@@C)<_>*b::bn(@@C)<1,i> 
  ensures i::cl(@@C)<a>*b::bn(@@C)<3,i> & a>=30;
{
  if (i.val<30)
  {                               // stage 1
    Barrier b;                    // stage 1->2
    i.val= i.val+1;
    Barrier b;                    // stage 2->1
    controll (i,b);
  }
  else Barrier b;                 // stage 1->3
}




