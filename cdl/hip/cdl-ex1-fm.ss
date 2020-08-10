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
  cell h, r;
  dprint;
  int v;
  CDL c = create_latch(2) with h'::cell<1> * r'::cell<2>;
  dprint;
  par {h, r, v, c@L}
  {
    case {h, c@L} c'::LatchIn{- h'::cell<1>}<> * c'::CNT<(1)> ->
      dprint;
      h = new cell(1);
      assert @lend[h'];
      countDown(c);
      dprint;
    ||
    case {r, c@L} c'::LatchIn{- r'::cell<2>}<> * c'::CNT<(1)> ->
      dprint;
      r = new cell(2);
      countDown(c);
      dprint;
    ||
    //else ->
    case {v, c@L} c'::LatchOut{+ h'::cell<1> * r'::cell<2> 
                    * @lend[h',r']}<> * c'::CNT<0> ->
      dprint;
      await(c);
      dprint;
      assert @lend[h'];
      assert @full[h'];
      assert @full[r'];
      assert @full[v];
      assert h'::cell<1>;
      assert r'::cell<2>;
      v = h.val + r.val;
      dprint;
  }
  //v = h.val + r.val;
  dprint;
  assert h'::cell<1> * r'::cell<2> & v' = 3;
  //assert h'::cell<1>;
}
