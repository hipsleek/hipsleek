/*

  Example for dynamic barriers:
  - thread 1 fully participates
  - thread 2 participates in one phase and drops out
  - thread 3 drops out immediately

 */

hip_include 'barrier_dynamic_header.ss'

//SUCCESS
void thread1(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(1,3,0)<2>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  waitBarrier(b);
  //phase 2
}

//SUCCESS
void thread2(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(0,3,-1)<1>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  removeParticipant(b,1);
}

//SUCCESS
void thread3(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(0,3,-1)<0>;
{
  //phase 0
  removeParticipant(b,1);
}

//SUCCESS
void main()
  requires true
  ensures true;
{
  barrier b = newBarrier(2);

  //oops, I want 1 more participant
  addParticipant(b,1);

  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);
  int id3 = fork(thread3,b);

  join(id1);
  join(id2);
  join(id3);

  destroyBarrier(b);

}
