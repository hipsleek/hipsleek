pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

void join2(thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

//memory cell
data cell{ int val;}

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures true;

thrd fork_thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures res::Thrd{+ x::cell<1> * y::cell<2>}<>;

thrd fork_thread2(thrd t1, cell y)
  requires t1::Thrd{+ y::cell<2>}<>
  ensures res::Thrd{+ y::cell<4>}<>;

void thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures x::cell<1> * y::cell<2>;
{
  x.val = x.val + 1;
  y.val = y.val + 2;
}

void thread2(thrd t1, cell y)
  requires t1::Thrd{+ y::cell<2>}<>
  ensures y::cell<4>;
{
  join2(t1);
  y.val = y.val + 2;
}

void main()
  requires true ensures true;
{

  cell x = new cell(0);
  cell y = new cell(0);

  thrd t1 = fork_thread1(x,y);
  thrd t2 = fork_thread2(t1,y);
  join2(t1);
  x.val = x.val + 1;
  join2(t2);
  assert x'::cell<2> * y'::cell<4>;
  destroyCell(x);
  destroyCell(y);
}
