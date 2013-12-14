/*
  A program with dynamic barriers.
  Inspired by the program Listing_13 at page 134-135 of
  A. Freeman. Pro .NET 4 Parallel Programming in C#. Apress, 2010.
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
  ensures b::barrier(0,2,-1)<0>;
{
  //phase 0
  //Bad task throwing exception
  //reduce the particpant count
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

  join(id1);
  join(id2);

  destroyBarrier(b);
}
