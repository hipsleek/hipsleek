/*
  An example with fork and multi-join.
  Joiners (main and t2) write-share the resource of the joinee (t1).

  Compile with "--en-para --en-thrd-resource -tp redlog"
 */

//memory cell
data cell{ int val;}

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures emp;

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
  requires emp ensures emp;
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
