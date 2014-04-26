/*
  The motivating example in Fig.1
 */

//memory cell
data cell{ int val;}

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures true;

void thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures x::cell<1> * y::cell<2>;
{
  x.val = x.val + 1;
  y.val = y.val + 2;
}

void thread2(thrd t1, cell y)
  requires t1::thrd<# y::cell<2> & true #>
  ensures y::cell<4>;
{
  join(t1);
  y.val = y.val + 2;
}

void main()
  requires true ensures true;
{

  cell x = new cell(0);
  cell y = new cell(0);

  thrd t1 = fork(thread1,x,y);
  thrd t2 = fork(thread2,t1,y);

  join(t1);
  x.val = x.val + 1;

  join(t2);

  assert x'::cell<2> * y'::cell<4>;

  destroyCell(x);
  destroyCell(y);
}
