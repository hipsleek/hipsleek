/*
  An example with fork and multi-join.
  Joiners (main and t2) write-share the resource of the joinee (t1).
 */

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<x:cell,y:cell>
inv x!=null & y!=null;
pred_prim THRD2{(+)Q@Split}<x:cell,y:cell>
inv x!=null & y!=null;

pred_prim THRD3{(-)P,(+)Q}<t1:thrd,y:cell>
inv y!=null;
pred_prim THRD4{(+)Q@Split}<t1:thrd,y:cell>
inv y!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<x,y> * self::dead<> -> %Q;

//this thread1 swaps the contents of x and y
thrd create_thrd1() // with %P
  requires true
  ensures (exists x,y: res::THRD{x::cell<vx> * y::cell<vy> & true,
                                 x::cell<vy> * y::cell<vx>}<x,y>);

void fork_thrd1(thrd t,cell x, cell y)
  requires t::THRD{%P,%Q}<x,y> * %P
  ensures  t::THRD2{%Q}<x,y>;

void join_thrd1(thrd t)
  requires exists x, y: t::THRD2{%Q}<x,y>
  ensures  t::dead<> * %Q;

// thread2
thrd create_thrd2() // with %P
  requires true
  ensures (exists t1,y: res::THRD3{t1::THRD2{y::cell<vy> & true}<_,y> & true,
                                   y::cell<vy+2>}<t1,y>);

void fork_thrd2(thrd t,thrd t1, cell y)
  requires t::THRD3{%P,%Q}<t1,y> * %P
  ensures  t::THRD4{%Q}<t1,y>;

void join_thrd2(thrd t)
  requires exists t1, y: t::THRD4{%Q}<t1,y>
  ensures  t::dead<> * %Q;
/**************************************/

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
  requires t1::THRD2{y::cell<vy> & true}<_,y>
  ensures y::cell<vy+2>;
{
  join_thrd1(t1);
  y.val = y.val + 2;
}

void main()
  requires emp ensures emp;
{

  cell x = new cell(1);
  cell y = new cell(2);

  thrd t1 = create_thrd1();
  thrd t2 = create_thrd2();


  fork_thrd1(t1,x,y);
  fork_thrd2(t2,t1,y);

  join_thrd1(t1);
  x.val = x.val + 1;

  join_thrd2(t2);

  assert x'::cell<3> * y'::cell<3>;

  destroyCell(x);
  destroyCell(y);
}
