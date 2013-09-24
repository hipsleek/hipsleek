/*
  Aliasing in bounded permissions needs special care.
  To ensure that before waitBarrier(b), there is
  exactly c=1 for barrier b, we need to first
  normalize the heap state and then conservatively perform
  a check_barrier_inconsistency().
  check_barrier_inconsistency() detect whether
  before waitBarrier(b1), there is a possibly
  aliased node b2. If so, conservatively reject.
 */

hip_include 'barrier_static_header.ss'

//need b1!=b2 to be able to waitBarrier(b1)
//FAIL-1
void participant_fail(barrier b1,barrier b2)
  requires b1::barrier(1,2,0)<0> * b2::barrier(1,2,0)<0>
  ensures b1::barrier(1,2,0)<1> * b2::barrier(1,2,0)<1>;
{
  waitBarrier(b1);
  waitBarrier(b2);
}

//SUCCESS
void participant(barrier b1,barrier b2)
  requires b1::barrier(1,2,0)<0> * b2::barrier(1,2,0)<0> & b1!=b2
  ensures b1::barrier(1,2,0)<1> * b2::barrier(1,2,0)<1>;
{
  waitBarrier(b1);
  waitBarrier(b2);
}

//SUCCESS
void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b1 = newBarrier(2);
  barrier b2 = newBarrier(2);
  int id1 = fork(participant,b1,b2);
  int id2 = fork(participant,b1,b2);
  join(id1);
  join(id2);
  destroyBarrier(b1);
  destroyBarrier(b2);
}

// need check_barrier_inconsistency() before waitBarrier()
// due to parameter aliasing
//SUCCESS
void main_fail()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b1 = newBarrier(2);
  barrier b2 = newBarrier(2);
  int id1 = fork(participant_fail,b1,b1);//participant_fail failed
  int id2 = fork(participant_fail,b2,b2);
  join(id1);
  join(id2);
  destroyBarrier(b1);
  destroyBarrier(b2);
}
