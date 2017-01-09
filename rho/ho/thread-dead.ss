/*
  General high-order primitives for threads.

  A thread carrying a cell.

  Resource carried by a dead thread is released
  by using the normalization lemma

 */

data cell{
  int v;
}

pred_prim THRD{(-)P,(+)Q}<x:cell,y:cell>
inv x!=null;

pred_prim THRD2{(+)Q@Split}<x:cell,y:cell>
inv x!=null;

pred_prim THRD3{(-)P,(+)Q}<t:thrd, x:cell>
inv x!=null;

pred_prim THRD4{(+)Q}<t:thrd, x:cell>
inv x!=null;

//after join
pred_prim dead<>
inv true;

/*
// this split is done during matching
lemma t::THRD2{%P * %Q}<x> -> t::THRD2{%P}<x> * t::THRD2{%Q}<x>;

*/

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<x,y> * self::dead<> -> %Q;

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists x,y: res::THRD{x::cell<vx> * y::cell<vy> & true,x::cell<vy> * y::cell<vx>}<x,y>);

void fork_thrd(thrd t,cell x, cell y)
  requires t::THRD{%P,%Q}<x,y> * %P
  ensures  t::THRD2{%Q}<x,y>;

void join_thrd(thrd t)
  requires exists x,y: t::THRD2{%Q}<x,y>
  ensures  t::dead<> * %Q;

// this new thread adds 3 to x
thrd create_thrd2() // with %P
  requires true
  ensures (exists x,t,y: res::THRD3{ t::THRD2{x::cell<vx>}<x,y> & true,t::dead<> * x::cell<vx+1>}<t,x>);

void fork_thrd2(thrd t2,thrd t, cell x)
  requires t2::THRD3{%P,%Q}<t,x> * %P
  ensures  t2::THRD4{%Q}<t,x>;

void join_thrd2(thrd t2)
  requires exists t,x: t2::THRD4{%Q}<t,x>
  ensures  t2::dead<> * %Q;

void destroy(cell c)
  requires c::cell<_>
  ensures emp;

void main()
  requires emp ensures emp;
{
  cell x = new cell(1);
  cell y = new cell(2);

  thrd tid1 =  create_thrd();
  thrd tid2 =  create_thrd2();

  fork_thrd(tid1,x,y); //(x=1,y=2) -> (x=2,y=1)
  fork_thrd2(tid2,tid1,x);

  //dprint;//2 threads here

  join_thrd2(tid2); //x=3
  //after joining with tid2, we know that tid1 is already dead
  //hence, we recover both x and y

  dprint; //tid1 still pending here. still need smart normalization here

  y.v = y.v +2; //y=3, y is released using "normalize" lemma

  dprint; // all threads are dead

  assert x'::cell<3> * y'::cell<3>;

  destroy(x);
  destroy(y);

}
