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
  cell h, r;
  int v;
  CDL c = create_latch(2) with h'::cell<1> * r'::cell<2> * @full[h, r];
  par {h, r, v, c@L}
  {
    case {h, c@L} c'::LatchIn{- h'::cell<1> * @full[h]}<> * c'::CNT<(1)> ->
      dprint;
      h = new cell(1);
      dprint;
      countDown(c);
      dprint;
    ||
    case {r, c@L} c'::LatchIn{- r'::cell<2> * @full[r]}<> * c'::CNT<(1)> ->
      r = new cell(2);
      countDown(c);
      dprint;
    ||
    //else ->
    case {v, c@L} c'::LatchOut{+ h'::cell<1> * r'::cell<2> * @full[h, r]}<> * c'::CNT<0> ->
      //dprint;
      await(c);
      v = h.val + r.val;
  }
  //dprint;
  assert h'::cell<1> * r'::cell<2> & v' = 3;
}

/*
# cdl-ex1-fm.ss

Above has been fixed by suitably adding @full to Latch..

*/
