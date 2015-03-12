//CountDownLatch
data CDL{
}

data cell{
  int v;
}

pred_prim LatchIn{(-)P}<x:cell>
inv x!=null;

pred_prim LatchOut{(+)P}<x:cell>
inv x!=null;

pred_prim CNT<n:int>;

lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a<=0 & b<=0 -> self::CNT<a+b>;

/********************************************/
CDL create_latch(int n) // with %P
  requires n>0
  ensures (exists x: res::LatchIn{x::cell<10>}<x> * res::LatchOut{x::cell<10>}<x> * res::CNT<n>);

void countDown(CDL c, cell a)
  requires c::LatchIn{%P}<a> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<n> & n<=0
  ensures c::CNT<n>;

void await(CDL c,cell a)
  requires c::LatchOut{%P}<a> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
  requires c::CNT<n> & n<0
  ensures c::CNT<n>;
/********************************************/

void destroyCell(cell c)
  requires c::cell<_>
  ensures emp;

void main()
  requires emp ensures emp;
{
  cell x = new cell(10);
  CDL c = create_latch(1);

  countDown(c,x);

  assert c'::CNT<0>;

  countDown(c,x);

  assert c'::CNT<0>;

  countDown(c,x);

  assert c'::CNT<0>;

  await(c,x);

  assert c'::CNT<(-1)>;

  await(c,x);

  assert c'::CNT<(-1)>;

  assert x'::cell<10>;

  destroyCell(x);
}

