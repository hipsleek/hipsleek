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
  cell h, r;
  int v;
  CDL c = create_latch(2) with h'::cell<_> * r'::cell<_>;
  par {h, r, v, c@L}
  {
    case {h, c@L} c'::LatchIn{- h'::cell<_>}<> * c'::CNT<(1)> ->
      h = new cell(1);
      countDown(c);
      //dprint;
    ||
    case {r, c@L} c'::LatchIn{- r'::cell<_>}<> * c'::CNT<(1)> ->
      r = new cell(2);
      countDown(c);
      //dprint;
    ||
    case {v, c@L} c'::LatchOut{+ h'::cell<_> * r'::cell<_>}<> * c'::CNT<0> ->
      dprint;
      await(c);
      dprint;
      v = h.val + r.val;
      //dprint;
  }
  //dprint;
  assert h'::cell<1> * r'::cell<2> & v' = 3; // Expected: ok
  assert h'::cell<2> * r'::cell<2> & v' = 3; // Expected: failed
  assert h'::cell<1> * r'::cell<3> & v' = 3; // Expected: failed
  assert h'::cell<1> * r'::cell<2> & v' = 4; // Expected: failed
}
