/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int v;
}

pred_prim LatchIn{-%P@Split}<x:cell>;

pred_prim LatchOut{+%P@Split}<x:cell>;
pred_prim CNT<n:int>
inv n>=(-1);

//lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

/********************************************/
CDL create_latch(int n) // with %P
  requires n>0
  ensures (exists x: res::LatchIn{-x::cell<10>}<x> * res::LatchOut{+x::cell<10>}<x> * res::CNT<n>);

void countDown(CDL c,cell x)
  requires c::LatchIn{-%P}<x> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<(-1)> 
  ensures c::CNT<(-1)>;

void await(CDL c,cell x)
  requires c::LatchOut{+%P}<x> * c::CNT<0>
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
  CDL c 
   = create_latch(1);
  dprint;
  countDown(c,x);


  await(c,x);

  //assert x'::cell<10>;

  //destroyCell(x);
}

/*
# ex2z-latch

Problem below is that we need to capture
ptrs in HO-arguments which is bad.

void countDown(CDL c,cell x)



*/
