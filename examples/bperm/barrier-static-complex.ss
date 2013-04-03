/*
  Example for static barriers.
  Inspired by the example in Figure 1(h) of the paper:
  "Barrier inference - POPL98".
  This example could not be handled in that work in specific,
  and by static analyses in general (I believe).
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

void thread1(barrier b, ref int i)
  requires b::barrier(1,2,0)<0> & i=0
  ensures b::barrier(1,2,0)<p> & p=i'-i & i'=10; //'
{
  while(i<10)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+i'-i & i<10 & i'=10
         or b::barrier(1,2,0)<p1> & p1=p & i>=10 & i'=i; //'
  {
    i=i+1;
    waitBarrier(b);
  }
}

void thread2(barrier b, ref int j)
  requires b::barrier(1,2,0)<0> & j=10
  ensures b::barrier(1,2,0)<p> & p=j'-j & j'=20; //'
{
  while(j<20)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+j'-j & j<20 & j'=20
         or b::barrier(1,2,0)<p1> & p1=p & j>=20 & j'=j; //'
  {
    j=j+1;
    waitBarrier(b);
  }
}

void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b = newBarrier(2);
  int i=0;
  int j=i+10;
  int id1 = fork(thread1,b,i);
  int id2 = fork(thread2,b,j);
  //dprint;
  join(id1);
  assert(i'=10);//'
  join(id2);
  assert(j'=20);//'
  //dprint;
  destroyBarrier(b);
  //dprint;
}




