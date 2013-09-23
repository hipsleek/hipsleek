/*
 Example for dynamic barriers
 (2013-04-28: currently used in Fig. 9)
 */

hip_include 'barrier_dynamic_header.ss'

//SUCCESS
void thread1(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<3>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  waitBarrier(b);
  //phase 2
  waitBarrier(b);
  //phase 3
}

//SUCCESS
void thread2(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(0,2,-1)<2>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  addParticipant(b,1);
  int id1 = fork(childthread1,b);
  int id2 = fork(childthread2,b);
  //...
  join(id1);
  join(id2);
}

//SUCCESS
void childthread1(barrier b)
  requires b::barrier(1,2,1/2)<1>
  ensures b::barrier(0,2,-1/2)<2>;
{
  waitBarrier(b);
  removeParticipant(b,1);
}

//SUCCESS
void childthread2(barrier b)
  requires b::barrier(1,2,1/2)<1>
  ensures b::barrier(0,2,-1/2)<1>;
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
  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);
  //dprint;
  join(id1);
  join(id2);
  //dprint;
  destroyBarrier(b);
  //dprint;
}
