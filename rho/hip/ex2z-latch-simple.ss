/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int v;
}

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;
pred_prim CNT<n:int>
inv n>=(-1);

//lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

/********************************************/
CDL create_latch(int n) with %P
  requires n>0
  ensures res::LatchIn{-%P}<> * res::LatchOut{+%P}<> * res::CNT<n>;
  requires n=0
  ensures res::CNT<(-1)>;

void countDown(CDL c)
  requires c::LatchIn{-%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<(-1)> 
  ensures c::CNT<(-1)>;

void await(CDL c)
  requires c::LatchOut{+%P}<> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
  requires c::CNT<(-1)>
  ensures c::CNT<(-1)> * %P;
/********************************************/

void destroyCell(cell c)
  requires c::cell<_>
  ensures emp;

void main()
  requires emp ensures emp;
{
  cell x = new cell(10);
  CDL c = create_latch(1) with x'::cell<_>;
  dprint;
  countDown(c);


  await(c);

  assert x'::cell<10>;

  //destroyCell(x);
}

/*
# ex2z-latch

Problem below is that we need to capture
ptrs in HO-arguments which is bad.

void countDown(CDL c,cell x)



*/
