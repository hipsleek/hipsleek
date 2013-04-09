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

void thread1(barrier b, int N)
  requires b::barrier(1,2,0)<p> & N>0
  ensures b::barrier(1,2,0)<p+2*N>; //'
{
  int i=0;
  while(i<2*N)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+i'-i & i<2*N & i'=2*N &b'=b
         or b::barrier(1,2,0)<p1> & p1=p & i>=2*N & i'=i & b'=b; //'
  {
    i=i+1;
    waitBarrier(b);
  }
}

void thread2(barrier b, int N)
  requires b::barrier(1,2,0)<p> & N>0
  ensures b::barrier(1,2,0)<p+2*N>; //'
{
  int i=0;
  while(i<N)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+i'-i & i<N & i'=N &b'=b & N'=N
         or b::barrier(1,2,0)<p1> & p1=p & i>=N & i'=i & b'=b & N'=N; //'
  {
    i=i+1;
    waitBarrier(b);
  }

  //...
  i=0;
  while(i<N)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+i'-i & i<N & i'=N &b'=b & N'=N
         or b::barrier(1,2,0)<p1> & p1=p & i>=N & i'=i & b'=b & N'=N; //'
  {
    i=i+1;
    waitBarrier(b);
  }
}

void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b = newBarrier(2);
  int N=10;
  int id1 = fork(thread1,b,N);
  int id2 = fork(thread2,b,N);
  join(id1);
  join(id2);
  destroyBarrier(b);
}




