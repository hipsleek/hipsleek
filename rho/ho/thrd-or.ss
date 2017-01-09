/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<c:cell>
inv c!=null;

pred_prim THRD2{(+)Q@Split}<c:cell>
inv c!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<c> * self::dead<> -> %Q;

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists c: res::THRD{ c::cell<_> & true ,
                                c::cell<1> or c::cell<2>
                               }<c>);

void fork_thrd(thrd t,cell h)
  requires t::THRD{%P,%Q}<h> * %P
  ensures  t::THRD2{%Q}<h>;

void join_thrd(thrd t)
  requires exists h: t::THRD2{%Q}<h>
  ensures  t::dead<> * %Q;
/**************************************/

data cell{
  int val;
}

void destroyCell(cell c)
  requires c::cell<_>
  ensures emp;

void main()
  requires emp ensures emp;
{
  cell x = new cell(0);
  thrd id = create_thrd();

  fork_thrd(id,x);

  dprint;
  join_thrd(id);

  dprint;
  assert x'::cell<v> & (v=1 | v=2); //'

  destroyCell(x);
}
