/*
  This example probably can not be handled by ESOP'11.
  Because ESOP'11 requires partipating threads proceeds in
  the same direction (same control flow);
  however, in this program, two threads
  does not necessary go in the same control flow.
 */

hip_include 'barrier_static_header.ss'

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




