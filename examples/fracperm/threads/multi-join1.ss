/*
  An example with fork and multi-join.
  Joiners (main and t2) share-write the resource of the joinee (t1).
 */

//memory cell
data cell{ int val;}

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures true;

void thread1(cell x, cell y)
  requires x::cell<vx> * y::cell<vy>
  ensures x::cell<vy> * y::cell<vx>;
{
  int tmp = x.val;
  x.val = y.val;
  y.val = tmp;
}

void thread2(thrd t1, cell y)
  requires t1::thrd<# y::cell<vy> & true #>
  ensures y::cell<vy+2>;
{
  join(t1);
  y.val = y.val + 2;
}

void main()
  requires true ensures true;
{

  cell x = new cell(1);
  cell y = new cell(2);

  thrd t1 = fork(thread1,x,y);
  thrd t2 = fork(thread2,t1,y);

  join(t1);
  x.val = x.val + 1;

  join(t2);

  assert x'::cell<3> * y'::cell<3>;

  destroyCell(x);
  destroyCell(y);
}
