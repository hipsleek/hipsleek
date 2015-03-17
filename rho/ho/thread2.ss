/*
  General high-order primitives for threads.

  A thread carrying a cell
 */

data cell{
  int v;
}

pred_prim THRD{P,Q}<x:cell>
inv x!=null;

pred_prim THRD2{Q}<x:cell>
inv x!=null;

//after join
pred_prim DEAD<>
inv true;

lemma t::THRD2{%P * %Q}<x> -> t::THRD2{%P}<x> * t::THRD2{%Q}<x>;
lemma t::THRD2{%P}<x> & t::DEAD<> -> %P;

// what is %P?
thrd create_thrd() // with %P
  requires true
  ensures (exists x: res::THRD{x::cell<vx> & true,x::cell<vx+1>}<x>);

void fork_thrd(thrd t,cell x)
  requires t::THRD{%P,%Q}<x> * %P
  ensures  t::THRD2{%Q}<x>;

void join_thrd(thrd t, cell x)
  requires t::THRD2{%Q}<x>
  ensures  t::DEAD<> * %Q;

void thread1(cell x)
  requires x::cell<vx>
  ensures x::cell<vx+1>;
{
  x.v = x.v + 1;
}

void main()
{
  cell x = new cell(1);

  thrd tid =  create_thrd();

  fork_thrd(tid,x);

  join_thrd(tid,x);

  assert x'::cell<2>;
}
