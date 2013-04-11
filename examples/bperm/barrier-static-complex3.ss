/*
  This example probably can not be handled by ESOP'11.
  Because ESOP'11 requires partipating threads proceeds in
  the same direction (same control flow);
  however, in this program, two threads
  does not necessary go in the same control flow.
 */

//permission rules for barrier
//********************************************
lemma "S-SPLIT" self::barrier(c,t,0)<p> & 0<c<=t & c=c1+c2 & 0<c1<t & 0<c2<t -> self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p>;

//combine successfully
lemma "S-COMBINE" self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p> -> self::barrier(c1+c2,t,0)<p>;

//detect inconsistency
 lemma "S-FAIL" self::barrier(c1,t,0)<p1> * self::barrier(c2,t,0)<p2> & p1!=p2 & flow __norm -> true & flow __Fail;
//********************************************

// WRAPPER FUNCTION
void destroyBarrier(ref barrier b)
  requires b::barrier(c,t,0)<_> & c=t
  ensures b'=null;//'

// WRAPPER FUNCTION
barrier newBarrier(int bound)
  requires bound>0
  ensures res::barrier(bound,bound,0)<0>;

// WRAPPER FUNCTION
void waitBarrier(barrier b)
  requires b::barrier(c,t,0)<p> & c=1
  ensures b::barrier(c,t,0)<p+1>;
//********************************************

void thread(barrier b, int n,int bs)
  requires (exists r1: b::barrier(1,2,0)<p> & n=r1*bs & n>0 & bs>0)
  ensures (exists r2: b::barrier(1,2,0)<p1> & n=r2*bs & p1-p=r2*3); //'
{
  int i=0;
  while(i<n)
    requires (exists r1,r2: b::barrier(1,2,0)<p> & n=r1*bs & i=r2*bs & r1>=r2 & bs>0)
    ensures b::barrier(1,2,0)<p1> & 3*(i'-i)=(p1-p)*bs & i<n & i'=n & bs'=bs & b'=b
         or b::barrier(1,2,0)<p1> & p1=p & i>=n & i'=i & bs'=bs & b'=b; //'
  {
    waitBarrier(b);//+1
    waitBarrier(b);//+1
    waitBarrier(b);//+1
    i=i+bs;
  }
}

void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b = newBarrier(2);
  int n;
  int bs;
  assume(exists r: n'=r*bs' & n'>0 & bs'>0);//'
  int id1 = fork(thread,b,n,bs);
  int id2 = fork(thread,b,n,bs);
  join(id1);
  join(id2);
  dprint;
  destroyBarrier(b);
}




