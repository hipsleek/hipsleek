/*
  This example probably can not be handled by ESOP'11.
  Because ESOP'11 requires partipating threads proceeds in
  the same direction (same control flow);
  however, in this program, two threads
  does not necessary go in the same control flow.
 */

hip_include 'barrier_static_header.ss'

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




