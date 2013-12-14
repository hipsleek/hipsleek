/*

  The example in Fig.12a of the report.
  We reject such inter-thread removal of participants

 */

hip_include 'barrier_dynamic_header.ss'

//FAIL
void thread1(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<2>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  removeParticipant(b,1); //FAIL
  //expect to remove
  //the participation of thread2
  //but is not allowed

  waitBarrier(b);
  //phase 1
}


//FAIL
void thread2(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(0,2,-1)<1>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  //no longer participate
  //expected to be remove by thread1
  //but is not allowed
}

//SUCCESS
void main()
  requires true
  ensures true;
{
  barrier b = newBarrier(2);

  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);

  join(id1);
  join(id2);

  destroyBarrier(b);

}
