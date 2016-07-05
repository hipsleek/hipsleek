/*

  The example of an incorrectly synchronized program in Fig. 5b
  of the report

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
  ensures b::barrier(1,2,0)<0>;
{
  ;
  //no-op
}

//FAIL
void main()
  requires emp
  ensures emp;
{
  barrier b = newBarrier(2);
  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);

  join(id1);
  join(id2); // FAIL, not b-consistent

  destroyBarrier(b);
}
