/* Example with simple CountDownLatch */

//CountDownLatch
data CDL {}

data cell { int val; }

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
  inv n>=(-1);

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

// Normalization lemma
lemma_prop "idemp-CNT" self::CNT<a> * self::CNT<(-1)> -> self::CNT<(-1)>;

lemma_prop "combine-CNT" self::CNT<a> * self::CNT<b> & a,b>=0 ->  self::CNT<a+b>;

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
  
/********************************************/
void main()
  requires emp ensures emp;
{
  cell x;
  int v = 1;
  CDL c = create_latch(1) with x'::cell<_> * @full[x];
  par {x, v, c@L}
  {
    case {x, c@L} c'::LatchIn{- x'::cell<_> * @full[x]}<> * c'::CNT<(1)> ->
      x = new cell(1);
      countDown(c);
      //dprint;
    ||
    case {v, c@L} c'::LatchOut{+ x'::cell<_> * @full[x]}<> * c'::CNT<0> ->
      await(c);
      v = x.val + v;
      //dprint;
  }
  //dprint;
  assert v' = 2; // Expected: ok
  assert v' = 3; // Expected: failed
}
