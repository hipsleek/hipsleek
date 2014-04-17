/*
  An example of t-inconsistency
 */

//memory cell
data cell{ int val;}

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures emp;

//VALID
void thread1(cell x, cell y)
  requires x::cell<vx> * y::cell<vy>
  ensures x::cell<vy> * y::cell<vx>;
{
  int tmp = x.val;
  x.val = y.val;
  y.val = tmp;
}

//as thread2 is the only one what joins with t1
//it should obtain both x and y
//VALID
void thread2(thrd t1, cell y)
  requires t1::thrd<# y::cell<vy> & true #>
  ensures y::cell<vy+2> & dead(t1);
{
  join(t1);
  y.val = y.val + 2;
}


//FAIL
void main()
  requires emp ensures emp;
{

  cell x = new cell(1);
  cell y = new cell(2);

  thrd t1 = fork(thread1,x,y);
  thrd t2 = fork(thread2,t1,y);

  /* dprint; */
  join(t2); //FAIL as t1 is both live and dead

  destroyCell(x);
  destroyCell(y);
}
