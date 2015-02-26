/*

  An example with fork and multi-join.
  Joiners (main and t2) read-share the resource of the joinee (t1).

  The resource is split using fractional permissions.
 */

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<x:cell,y:cell>
inv x!=null & y!=null;
pred_prim THRD2{(+)Q@Split}<x:cell,y:cell>
inv x!=null & y!=null;

pred_prim THRD3{(-)P,(+)Q}<t1:thrd,x:cell,y:cell>
inv x!=null & y!=null;
pred_prim THRD4{(+)Q@Split}<t1:thrd,x:cell,y:cell>
inv x!=null & y!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<x,y> * self::dead<> -> %Q;

//this thread1 swaps the contents of x and y
thrd create_thrd1() // with %P
  requires true
  ensures (exists x,y: res::THRD{x::cell<0> * y::cell<0> & true,
                                 x::cell<1> * y::cell<2>}<x,y>);

void fork_thrd1(thrd t,cell x, cell y)
  requires t::THRD{%P,%Q}<x,y> * %P
  ensures  t::THRD2{%Q}<x,y>;

void join_thrd1(thrd t)
  requires exists x, y: t::THRD2{%Q}<x,y>
  ensures  t::dead<> * %Q;

// thread2
thrd create_thrd2() // with %P
  requires true
  ensures (exists t1,x,y: res::THRD3{t1::THRD2{x::cell(0.6)<1>@S1 * y::cell(0.6)<2>@S1 & true}<x,y> & true,
                                     x::cell(0.6)<1> * y::cell(0.6)<2>}<t1,x,y>);

void fork_thrd2(thrd t,thrd t1, cell x, cell y)
  requires t::THRD3{%P,%Q}<t1,x,y> * %P
  ensures  t::THRD4{%Q}<t1,x,y>;

void join_thrd2(thrd t)
  requires exists t1, x, y: t::THRD4{%Q}<t1,x,y>
  ensures  t::dead<> * %Q;
/**************************************/

//memory cell
data cell{ int val;}

//fractional permission split for cell
lemma_split "splitCell" self::cell(f)<v> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::cell(f1)<v> * self::cell(f2)<v> & 0.0<f<=1.0;

////fractional permission combine for cell
lemma "combineCell" self::cell(f1)<v> * self::cell(f2)<v> -> self::cell(f1+f2)<v>;

/* // */

//deallocate a cell
void destroyCell(cell a)
  requires a::cell<_>
  ensures emp;

void thread1(cell x, cell y)
  requires x::cell<0> * y::cell<0>
  ensures x::cell<1> * y::cell<2>;
{
  x.val = x.val + 1;
  y.val = y.val + 2;
}

void thread2(thrd t1, cell x, cell y)
  requires t1::THRD2{x::cell(0.6)<1>@S1 * y::cell(0.6)<2>@S1 & true}<x,y>
  ensures x::cell(0.6)<1> * y::cell(0.6)<2>;
{
  join_thrd1(t1);
  int a = x.val + y.val;
  assert a'=3; //'
}

void main()
  requires emp ensures emp;
{

  cell x = new cell(0);
  cell y = new cell(0);

  thrd t1 = create_thrd1();
  thrd t2 = create_thrd2();

  fork_thrd1(t1,x,y);
  fork_thrd2(t2,t1,x,y); //fractional split of resource required

  join_thrd1(t1);
  int a = x.val + y.val;
  assert a'=3; //'

  join_thrd2(t2);

  assert x'::cell<1> * y'::cell<2>;

  destroyCell(x);
  destroyCell(y);
}
