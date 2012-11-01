
// one centralized producer 1 different workers consuming the same data.

data cl {int val;}

macro L == (#,) 
macro R == (,#) 

Barrier bn[2]<int state, cl i> == [
 (0,1,[ requires i::cl(@@L)<T1>*self::bn(@@L)<0,i> ensures i::cl(@@L)<T1>*self::bn(@@L)<1,i> ;,
		requires i::cl(@@R)<T2>*self::bn(@@R)<0,i> ensures i::cl(@@R)<T2>*self::bn(@@R)<1,i>;]),	
 (1,2,[ requires i::cl(@@L)<T> *self::bn(@@L)<1,i> & T<30  ensures i::cl<T>* self::bn(@@L)<2,i> & T<30 ;,
		requires i::cl(@@R)<T> *self::bn(@@R)<1,i> & T<30  ensures 			self::bn(@@R)<2,i>;]),
 (2,1,[ requires 				self::bn(@@R)<2,i>		   ensures i::cl(@@R)<T>*self::bn(@@R)<1,i>;,
		requires i::cl<T>*self::bn(@@L)<2,i>  			   ensures i::cl(@@L)<T>*self::bn(@@L)<1,i>;]) ,
 (1,3,[ requires i::cl(@@L)<T> *self::bn(@@L)<1,i> & T>=30 ensures i::cl<T>*self::bn(@@L)<3,i>& T>=30;, 
		requires i::cl(@@R)<T> *self::bn(@@R)<1,i> & T>=30 ensures self::bn(@@R)<3,i>;])];

void th (cl i, barrier b)
requires i::cl(@@R)<_>*b::bn(@@R)<0,i> 
 ensures b::bn(@@R)<3,i>;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  thl (i,b);
}
 
void thl(cl i, barrier b)
requires i::cl(@@R)<_>*b::bn(@@R)<1,i> 
  ensures b::bn(@@R)<3,i>;
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
requires i::cl(@@L)<1>*b::bn(@@L)<0,i> 
 ensures i::cl(@@L)<a>*b::bn(@@L)<3,i> & a>=30;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  controll (i,b);
}
 
void controll(cl i, barrier b)
requires i::cl(@@L)<_>*b::bn(@@L)<1,i> 
  ensures i::cl(@@L)<a>*b::bn(@@L)<3,i> & a>=30;
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




