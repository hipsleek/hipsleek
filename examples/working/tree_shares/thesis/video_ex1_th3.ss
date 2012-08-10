data cl {int val;}

macro L == (#,) 
macro R == (,(#,)) 
macro RR == (,(,#)) 
macro WL == (,#)

Barrier bn[3]<int state, cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i> == [(0,1,[
 requires x1::cl(@@L)<A2>*x2::cl(@@L)<B2>*y1::cl(@@L)<C2>*y2::cl(@@L)<D2>*x3::cl(@@L)<E1>*y3::cl(@@L)<E2>*i::cl(@@L)<T1>*self::bn(@@L)<0,x1,x2,y1,y2,x3,y3,i> 
        ensures x1::cl(@@L)<A1>*x2::cl(@@L)<B2>*x3::cl(@@L)<E1>*y1::cl<C1>*i::cl(@@L)<T1>*self::bn(@@L)<1,x1,x2,y1,y2,x3,y3,i> ;,
 requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y1::cl(@@R)<C2>*y2::cl(@@R)<D2>*y3::cl(@@R)<E2>*i::cl(@@R)<T2>*self::bn(@@R)<0,x1,x2,y1,y2,x3,y3,i> 
        ensures x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y2::cl<D2>*i::cl(@@R)<T2>*self::bn(@@R)<1,x1,x2,y1,y2,x3,y3,i>;,
  requires x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y1::cl(@@RR)<C2>*y2::cl(@@RR)<D2>*y3::cl(@@RR)<E2>*i::cl(@@RR)<T2>*self::bn(@@RR)<0,x1,x2,y1,y2,x3,y3,i> 
        ensures x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y3::cl<E2>*i::cl(@@RR)<T2>*self::bn(@@RR)<1,x1,x2,y1,y2,x3,y3,i>;		
]),	
 (1,2,[
 requires x1::cl(@@L)<A1>*x2::cl(@@L)<B1>*x3::cl(@@L)<E1>*y1::cl<C1>*i::cl(@@L)<T>*self::bn(@@L)<1,x1,x2,y1,y2,x3,y3,i> & T<30
	ensures x1::cl<A2>*y1::cl(@@L)<C1> * y2::cl(@@L)<D2>*y3::cl(@@L)<E2> * i::cl<T>* self::bn(@@L)<2,x1,x2,y1,y2,x3,y3,i> & T<30 ;,
	
 requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y2::cl<D2>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,x3,y3,i>&T<30
    ensures x2::cl<B2>*y1::cl(@@R)<C1>*y2::cl(@@R)<D2>*y3::cl(@@R)<E2>*         self::bn(@@R)<2,x1,x2,y1,y2,x3,y3,i>;,
	
 requires  x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y3::cl<E2>*i::cl(@@RR)<T>*self::bn(@@RR)<1,x1,x2,y1,y2,x3,y3,i> & T<30
    ensures x3::cl<E1>*y1::cl(@@RR)<C1>*y2::cl(@@RR)<D2>*y3::cl(@@RR)<E2>*         self::bn(@@RR)<2,x1,x2,y1,y2,x3,y3,i>;
	]),
    
 (2,1,[
 requires x1::cl<A1>*y1::cl(@@L)<C1> * y2::cl(@@L)<D2>*y3::cl(@@L)<E2> * i::cl<T>* self::bn(@@L)<2,x1,x2,y1,y2,x3,y3,i>
	ensures x1::cl(@@L)<A2>*x2::cl(@@L)<B1>*x3::cl(@@L)<E1>*y1::cl<C1>*i::cl(@@L)<T>*self::bn(@@L)<1,x1,x2,y1,y2,x3,y3,i> ;,
	
 requires x2::cl<B2>*y1::cl(@@R)<C1>*y2::cl(@@R)<D2>*y3::cl(@@R)<E2>*         self::bn(@@R)<2,x1,x2,y1,y2,x3,y3,i>
	ensures x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y2::cl<D2>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,x3,y3,i>;,
	
 requires x3::cl<E1>*y1::cl(@@RR)<C1>*y2::cl(@@RR)<D2>*y3::cl(@@RR)<E2>*         self::bn(@@RR)<2,x1,x2,y1,y2,x3,y3,i>
	ensures x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y3::cl<E2>*i::cl(@@RR)<T>*self::bn(@@RR)<1,x1,x2,y1,y2,x3,y3,i>;
  ]) ,
 
 (1,3,[
  requires x1::cl(@@L)<A1>*x2::cl(@@L)<B1>*x3::cl(@@L)<E1>*y1::cl<C1>*i::cl(@@L)<T>*self::bn(@@L)<1,x1,x2,y1,y2,x3,y3,i> & T>=30
	ensures x1::cl(@@L)<A>*x2::cl(@@L)<B>*i::cl<T>*self::bn(@@L)<3,x1,x2,y1,y2,x3,y3,i>& T>=30 ;,
	
 requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y2::cl<D2>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,x3,y3,i>&T>=30
    ensures x1::cl(@@WL)<A>*x2::cl(@@WL)<B>         *self::bn(@@R)<3,x1,x2,y1,y2,x3,y3,i>;,
	
 requires  x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y3::cl<E2>*i::cl(@@RR)<T>*self::bn(@@RR)<1,x1,x2,y1,y2,x3,y3,i> & T>=30
    ensures x3::cl<E1>*y1::cl<C1>*y2::cl<D2>*y3::cl<E2>*         self::bn(@@RR)<3,x1,x2,y1,y2,x3,y3,i>;
  ])];

void th3 (cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y1::cl(@@RR)<C2>*y2::cl(@@RR)<D2>*y3::cl(@@RR)<E2>*i::cl(@@RR)<T2>*b::bn(@@RR)<0,x1,x2,y1,y2,x3,y3,i> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th3_loop (x1,x2,y1,y2,x3,y3,i,b);
}
 
void th3_loop(cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@RR)<A2>*x2::cl(@@RR)<B2>*x3::cl(@@RR)<E1>*y3::cl<E2>*i::cl(@@RR)<T>*b::bn(@@RR)<1,x1,x2,y1,y2,x3,y3,i>
  ensures true;
{
  if (i.val<30)
  {                               // stage 1
    y3.val = x1.val + x2.val+x3.val;
    Barrier b;                    // stage 1->2
    x3.val = y1.val - y2.val-y3.val;
    Barrier b;                    // stage 2->1
    th3_loop (x1,x2,y1,y2,x3,y3,i,b);
  }
  else Barrier b;                 // stage 1->3
}

void th2 (cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y1::cl(@@R)<C2>*y2::cl(@@R)<D2>*y3::cl(@@R)<E2>*i::cl(@@R)<T2>*b::bn(@@R)<0,x1,x2,y1,y2,x3,y3,i> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th2_loop (x1,x2,y1,y2,x3,y3,i,b);
}
 
void th2_loop(cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*x3::cl(@@R)<E1>*y2::cl<D2>*i::cl(@@R)<T>*b::bn(@@R)<1,x1,x2,y1,y2,x3,y3,i>
  ensures true;
{
  if (i.val<30)
  {                               // stage 1
    y2.val = x1.val + x2.val+x3.val;
    Barrier b;                    // stage 1->2
    x2.val = y1.val - y2.val-y3.val;
    Barrier b;                    // stage 2->1
    th2_loop (x1,x2,y1,y2,x3,y3,i,b);
  }
  else Barrier b;                 // stage 1->3
}

 
void th1 (cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@L)<A2>*x2::cl(@@L)<B2>*y1::cl(@@L)<C2>*y2::cl(@@L)<D2>*x3::cl(@@L)<E1>*y3::cl(@@L)<E2>*i::cl(@@L)<T1>*b::bn(@@L)<0,x1,x2,y1,y2,x3,y3,i> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th1_loop (x1,x2,y1,y2,x3,y3,i,b);
}
 
void th1_loop(cl x1, cl x2, cl y1, cl y2, cl x3, cl y3, cl i, barrier b)
requires x1::cl(@@L)<A1>*x2::cl(@@L)<B1>*x3::cl(@@L)<E1>*y1::cl<C1>*i::cl(@@L)<T>*b::bn(@@L)<1,x1,x2,y1,y2,x3,y3,i>
  ensures true;
{
  if (i.val<30)
  {                               // stage 1
    y1.val = x1.val + 2*x2.val+2+x3.val;
    Barrier b;                    // stage 1->2
    x1.val = y1.val - y2.val-y3.val;
    i.val= i.val+1;
    Barrier b;                    // stage 2->1
    th1_loop (x1,x2,y1,y2,x3,y3,i,b);
  }
  else Barrier b;                 // stage 1->3
}
