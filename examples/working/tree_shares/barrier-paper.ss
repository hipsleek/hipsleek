data cl {int val;}

macro L == (#,) 
macro R == (,#) 

Barrier bn[2]<int state, cl x1, cl x2, cl y1, cl y2, cl i> == [(0,1,[
 requires x1::cl(@@L)<A1>*x2::cl(@@L)<B1>*y1::cl(@@L)<C1>*y2::cl(@@L)<D1>*i::cl(@@L)<T1>*self::bn(@@L)<0,x1,x2,y1,y2,i> 
        ensures x1::cl(@@L)<A1>*x2::cl(@@L)<B1>*y1::cl<C1>*i::cl(@@L)<T1>*self::bn(@@L)<1,x1,x2,y1,y2,i> ;,
 requires x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*y1::cl(@@R)<C2>*y2::cl(@@R)<D2>*i::cl(@@R)<T2>*self::bn(@@R)<0,x1,x2,y1,y2,i> 
        ensures x1::cl(@@R)<A2>*x2::cl(@@R)<B2>*y2::cl<D2>*i::cl(@@R)<T2>*self::bn(@@R)<1,x1,x2,y1,y2,i>;]),	
 (1,2,[
 requires x1::cl(@@L)<A> * x2::cl(@@L)<B>*y1::cl<C> * i::cl(@@L)<T> * self::bn(@@L)<1,x1,x2,y1,y2,i> & T<30
    
	ensures x1::cl<A>*y1::cl(@@L)<C> * y2::cl(@@L)<D>*i::cl<T>* self::bn(@@L)<2,x1,x2,y1,y2,i> & T<30 ;,
	
 requires x1::cl(@@R)<A>*x2::cl(@@R)<B>*y2::cl<D>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,i>&T<30
    ensures x2::cl<B>*y1::cl(@@R)<C>*y2::cl(@@R)<D>*         self::bn(@@R)<2,x1,x2,y1,y2,i>;]),
    
 (2,1,[
 requires x2::cl<B>*y1::cl(@@R)<C>*y2::cl(@@R)<D>*         self::bn(@@R)<2,x1,x2,y1,y2,i>
    ensures x1::cl(@@R)<A>*x2::cl(@@R)<B>*y2::cl<D>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,i>;,
 requires x1::cl<A>*y1::cl(@@L)<C>*y2::cl(@@L)<D>*i::cl<T>*self::bn(@@L)<2,x1,x2,y1,y2,i> 
    ensures x1::cl(@@L)<A>*x2::cl(@@L)<B>*y1::cl<C>*i::cl(@@L)<T>*self::bn(@@L)<1,x1,x2,y1,y2,i>;]) ,
 
 (1,3,[
 requires x1::cl(@@L)<A>*x2::cl(@@L)<B>*i::cl(@@L)<T>*self::bn(@@L)<1,x1,x2,y1,y2,i>& T>=30 
    ensures x1::cl(@@L)<A>*x2::cl(@@L)<B>*i::cl<T>*self::bn(@@L)<3,x1,x2,y1,y2,i>& T>=30;, 
 requires x1::cl(@@R)<A>*x2::cl(@@R)<B>*i::cl(@@R)<T>*self::bn(@@R)<1,x1,x2,y1,y2,i>& T>=30 
    ensures x1::cl(@@R)<A>*x2::cl(@@R)<B>         *self::bn(@@R)<3,x1,x2,y1,y2,i>;])];


void close (channel y) requires y::channel<> ensures true;
channel close () requires true ensures res::channel<>;
 
void th2 (cl x1, cl x2, cl y1, cl y2, cl i, barrier b)
requires x1::cl(@@R)<1>*x2::cl(@@R)<1>*y1::cl(@@R)<_>*y2::cl(@@R)<_>*i::cl(@@R)<1>*b::bn(@@R)<0,x1,x2,y1,y2,i> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th2_loop (x1,x2,y1,y2,i,b);
}
 
void th2_loop(cl x1, cl x2, cl y1, cl y2, cl i, barrier b)
requires x1::cl(@@R)<_>*x2::cl(@@R)<_>*y2::cl<_>*i::cl(@@R)<a>*b::bn(@@R)<1,x1,x2,y1,y2,i> 
  ensures true;
{
  if (i.val<30)
  {                               // stage 1
    y2.val = x1.val + x2.val;
    Barrier b;                    // stage 1->2
    x2.val = y1.val - y2.val;
    Barrier b;                    // stage 2->1
    th2_loop (x1,x2,y1,y2,i,b);
  }
  else Barrier b;                 // stage 1->3
}

 
void th1 (cl x1, cl x2, cl y1, cl y2, cl i, barrier b)
requires x1::cl(@@L)<1>*x2::cl(@@L)<1>*y1::cl(@@L)<_>*y2::cl(@@L)<_>*i::cl(@@L)<1>*b::bn(@@L)<0,x1,x2,y1,y2,i> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th1_loop (x1,x2,y1,y2,i,b);
}
 
void th1_loop(cl x1, cl x2, cl y1, cl y2, cl i, barrier b)
requires x1::cl(@@L)<_>*x2::cl(@@L)<_>*y1::cl<_>*i::cl(@@L)<a>*b::bn(@@L)<1,x1,x2,y1,y2,i> 
  ensures true;
{
  if (i.val<30)
  {                               // stage 1
    y1.val = x1.val + 2*x2.val+2;
    Barrier b;                    // stage 1->2
    x1.val = y1.val - y2.val;
    i.val= i.val+1;
    Barrier b;                    // stage 2->1
    th1_loop (x1,x2,y1,y2,i,b);
  }
  else Barrier b;                 // stage 1->3
}
