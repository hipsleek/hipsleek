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
  cell p, q;
  CDL c = create_latch(2) with p'::cell<1> * q'::cell<2> * @full[p', q'];
  //dprint;
  par {p, q, c@L}
  {
    case {p, c@L} c'::LatchIn{- p'::cell<1> * @full[p']}<> * c'::LatchOut{+ q'::cell<2> * @full[q']}<> * c'::CNT<(1)> ->
      p = new cell(1);
      countDown(c);
      await(c);
      q.val = q.val + 1; 
      dprint;
      assert q'::cell<3>;
    ||
    case {q, c@L} c'::LatchIn{- q'::cell<2> * @full[q']}<> *  c'::LatchOut{+ p'::cell<1>  * @full[p']}<> * c'::CNT<(1)> ->
      q = new cell(2);
      countDown(c);
      await(c);
      p.val = p.val + 1;
      dprint;
      assert p'::cell<2>;
  }
  dprint;
  assert p'::cell<2> * q'::cell<3> * c'::CNT<(-1)>; // ok
  assert p'::cell<2> * q'::cell<3> * c'::CNT<a> & a >= 0; // failed
  assert p'::cell<3> * q'::cell<3>; // failed
  assert p'::cell<2> * q'::cell<4>; // failed
  assert p'::cell<3> * q'::cell<4>; // failed
}
