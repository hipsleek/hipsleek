/*

  The complex example in Fig. 7 of the report.

  This complex example could not be handled by existing works.

 */

hip_include 'barrier_static_header.ss'

void thread1(barrier b, int N)
  requires b::barrier(1,2,0)<0> & N=10
  ensures b::barrier(1,2,0)<20>; //'
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
  requires b::barrier(1,2,0)<0> & N=10
  ensures b::barrier(1,2,0)<20>; //'
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
  requires emp
  ensures emp;
{
  barrier b = newBarrier(2);
  int N=10;

  int id1 = fork(thread1,b,N);
  int id2 = fork(thread2,b,N);

  join(id1);
  join(id2);

  destroyBarrier(b);
}
