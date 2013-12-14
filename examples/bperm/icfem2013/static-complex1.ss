/*
  Example for static barriers.
  Inspired by the example in Figure 1(h) of the paper:
  "Barrier inference - POPL98".
  This example could not be handled in that work in specific,
  and by static analyses in general.
 */

hip_include 'barrier_static_header.ss'

void thread1(barrier b, ref int i)
  requires b::barrier(1,2,0)<0> & i=0
  ensures b::barrier(1,2,0)<p> & p=i'-i & i'=10; //'
{
  while(i<10)
    requires b::barrier(1,2,0)<p>
    ensures b::barrier(1,2,0)<p1> & p1=p+i'-i & i<10 & i'=10 &b'=b
         or b::barrier(1,2,0)<p1> & p1=p & i>=10 & i'=i & b'=b; //'
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
    ensures b::barrier(1,2,0)<p1> & p1=p+j'-j & j<20 & j'=20 & b'=b
         or b::barrier(1,2,0)<p1> & p1=p & j>=20 & j'=j & b'=b; //'
  {
    j=j+1;
    waitBarrier(b);
  }
}

void main()
  requires emp
  ensures emp;
{
  barrier b = newBarrier(2);
  int i=0;
  int j=i+10;
  int id1 = fork(thread1,b,i);
  int id2 = fork(thread2,b,j);

  join(id1);
  assert(i'=10);//'
  join(id2);
  assert(j'=20);//'

  destroyBarrier(b);

}




