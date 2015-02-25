/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL {}

data cell { int val; }

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
  inv n>=(-1);

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

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
  ensures c::CNT<(-1)>;
  
void main()
  requires emp ensures emp;
{
  cell p, q;
  CDL c = create_latch(1) with p'::cell<_> * q'::cell<_>;
  par {p, q, c@L}
  {
    case {p, q, c@L} c'::LatchIn{- p'::cell<_> * q'::cell<_>}<> * c'::CNT<(1)> ->
      dprint;
      p = new cell(1);
      q = new cell(2);
      countDown(c);
    ||
    case {c@L} c'::LatchOut{+ p'::cell<_>}<> * c'::CNT<(0)> ->
      await(c);
      p.val = p.val + 1;
    ||
    //else ->
    case {c@L} c'::LatchOut{+ q'::cell<_>}<> * c'::CNT<0> ->
      await(c);
      q.val = q.val + 1;
  }
  //dprint;
  assert p'::cell<2> * q'::cell<3>; // ok
  assert p'::cell<3> * q'::cell<3>; // failed
  assert p'::cell<2> * q'::cell<4>; // failed
  assert p'::cell<3> * q'::cell<4>; // failed
}
