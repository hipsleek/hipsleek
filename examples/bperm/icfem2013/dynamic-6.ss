/*
  A program with dynamic barriers.
  Inspired by the program Listing_13 at page 529-530 of
  E. Bill et. al. . NET 4 Wrox PDF Bundle . John Wiley & Sons, Inc, 2010.
 */

hip_include 'barrier_dynamic_header.ss'

//SUCCESS
void CalculationInTask(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(0,3,-1)<0>;
{
  // do calculation

  //calculation complete
  removeParticipant(b,1);
}

//SUCCESS
void main()
  requires true
  ensures true;
{
  int numberTasks = 2;
  barrier b = newBarrier(numberTasks+1);

  int id1 = fork(CalculationInTask,b);
  int id2 = fork(CalculationInTask,b);

  //wait for all tasks to complete
  waitBarrier(b);
  //compute the result

  join(id1);
  join(id2);

  destroyBarrier(b);
}
