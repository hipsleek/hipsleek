/*

  The example in Fig.12b of the report.

  The program is readily verified as correctly synchronized.

 */

hip_include 'barrier_dynamic_header.ss'

//SUCCESS
void thread1(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<2>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  waitBarrier(b);
  //phase 2
}


//SUCCESS
void thread2(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(0,2,-1)<1>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  //no longer participate

  removeParticipant(b,1); //deliberately drop its participation
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
