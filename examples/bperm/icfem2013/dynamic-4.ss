/*
  Program with dynamic barriers.
  Inspired by the program "BarrierDemo" at
  http://msdn.microsoft.com/en-us/library/system.threading.barrier.aspx
 */

hip_include 'barrier_dynamic_header.ss'

//SUCCESS
// This is the logic run by all participants
void thread(barrier b)
  requires b::barrier(1,4,0)<0>
  ensures b::barrier(1,4,0)<4>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  waitBarrier(b);
  //phase 2
  waitBarrier(b);
  //phase 3
  waitBarrier(b);
  //phase 4
}


void parallel_invoke(barrier b)
  requires b::barrier(4,4,0)<0>
  ensures b::barrier(4,4,0)<_>;
{
  int id1 = fork(thread,b);

  int id2 = fork(thread,b);

  int id3 = fork(thread,b);

  int id4 = fork(thread,b);

  join(id1);
  join(id2);
  join(id3);
  join(id4);
}

//SUCCESS
void main()
  requires true
  ensures true;
{
  // Create a barrier with three participants
  barrier b = newBarrier(3);

  // Nope -- changed my mind.  Let's make it five participants.
  addParticipant(b,2);

  // Nope -- let's settle on four participants.
  removeParticipant(b,1);

  /* Now launch 4 parallel actions to serve as 4 participants */
  parallel_invoke(b);

  destroyBarrier(b);
}
