/*
 Example for static barriers
 */

hip_include 'barrier_static_header.ss'

void thread1(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<1>;
{
  waitBarrier(b);
}

void thread2(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<1>;
{
  waitBarrier(b);
}

void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b = newBarrier(2);
  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);
  //dprint;
  join(id1);
  join(id2);
  //dprint;
  destroyBarrier(b);
  //dprint;
}
