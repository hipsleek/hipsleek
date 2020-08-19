/*
  Example with simple CountDownLatch
*/

//CountDownLatch
data CDL {}

data cell { int val; }

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int> @ThreadLocal
  inv n>=(-1);

lemma "norm" self::CNT<a> * self::CNT<(-1)> & a<=0 -> self::CNT<(-1)>.

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

lemma "error" self::CNT<a> * self::CNT<b> & a>0 & b<0 ->  emp & flow __Fail.

lemma "release" self::LatchOut{+%P}<> * self::CNT<n> & n<0 -> %P.

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

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
  ensures c::CNT<(-1)>;
  
void main()
  requires emp ensures emp;
{
  cell x = new cell(10);
  //dprint;
  CDL c = create_latch(1) with x'::cell<_>;
  //dprint;
  countDown(c);
  //dprint;
  assert x'::cell<10>; // fail
  await(c);
  //dprint;
  assert x'::cell<10>; // ok
  assert x'::cell<11>; // fail 
}
