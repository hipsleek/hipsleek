/*
  BUGGY
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
  ensures (exists x,vx: res::THRD{x::cell<vx> & true,x::cell<vx+1>}<x>);

void fork_thrd(thrd t,cell xxx)
  requires t::THRD{%P,%Q}<xxx> * %P
  ensures  t::THRD2{%Q}<xxx>;

//BUG: if removing exists yyy
void join_thrd(thrd t)
  requires (exists yyy: t::THRD2{%Q}<yyy>)
  ensures  t::DEAD<> * %Q;

/*
void thread1(cell zzz)
  requires zzz::cell<vx>
  ensures x::cell<vx+1>;
{
  x.v = x.v + 1;
}
*/

void main()
{
  cell x = new cell(1);

  thrd tid =  create_thrd();

  fork_thrd(tid,x);

  dprint;
  join_thrd(tid);
  dprint;

  assert x'::cell<2>;
}
