data cl {int val;}

macro L == (#,)
macro R == (,#)

Barrier bn[2]<int state, cl x1> == [(0,1,[
 requires x1::cl(@@L)<A1>*self::bn(@@L)<0,x1>
 ensures self::bn(@@L)<1,x1> ;,
 requires x1::cl(@@R)<A2>*self::bn(@@R)<0,x1>
 ensures x1::cl<A2> * self::bn(@@R)<1,x1>;
 ]),
 (1,2,[
 requires self::bn(@@L)<1,x1>
 ensures  x1::cl<A1> * self::bn(@@L)<2,x1>;,
 requires x1::cl<A2> *self::bn(@@R)<1,x1>
 ensures  self::bn(@@R)<2,x1>;
 ])
 
 ];

void th2 (cl x1, int deposit, barrier b)
requires x1::cl(@@R)<1>*b::bn(@@R)<0,x1> 
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th2_loop (x1, deposit, b);
}

void th2_loop(cl x1, int deposit, barrier b)
requires x1::cl<_>*b::bn(@@R)<1,x1>
  ensures true;
{
    x1.val = x1.val + deposit;
    Barrier b;                 // stage 1->2
}


void th1 (cl x1, int withdraw, barrier b)
requires x1::cl(@@L)<1>*b::bn(@@L)<0,x1>
 ensures true;
{                                 // stage 0
  Barrier b;                      // stage 0->1
  th1_loop (x1, withdraw, b);
}


void th1_loop(cl x1, int withdraw, barrier b)
requires b::bn(@@L)<1,x1>
ensures true;
{
  Barrier b;                 // stage 1->2
  x1.val = x1.val - withdraw;
}
