/*
  Check for db-consistency in frame rule and par rule
  Frame rule -> check post-condition
  Par rule -> check join()
 */

hip_include 'barrier_static_header.ss'

//need b1!=b2 to be able to waitBarrier(b1)
//FAIL-1
void participant_fail(barrier b1,barrier b2)
  requires b1::barrier(1,2,0)<0> * b2::barrier(1,2,0)<0>
  ensures b1::barrier(1,2,0)<1> * b2::barrier(1,2,0)<1>;
{
  waitBarrier(b1);//possible inconsistency detected
  //because b1 and b2 may alias and have different phase numbers
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

void participant1(barrier b1)
  requires b1::barrier(1,2,0)<p>
  ensures b1::barrier(1,2,0)<p+1>;
{
  waitBarrier(b1);
}

//FAIL-1
void main_fail()
  requires emp
  ensures emp;
{
  barrier b1 = newBarrier(2);
  int id1 = fork(participant1,b1);
  join(id1); //inconsistent detected when join()
  // as two nodes of barrier b1 have different phase numbers
  destroyBarrier(b1);
}

// need check_barrier_inconsistency() in
// post-cond (frame rule) and join() (par rule)
// due to parameter aliasing
//SUCCESS
void main()
  requires emp
  ensures emp;
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
