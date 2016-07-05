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

// Normalization lemma
lemma_prop "idemp-CNT" self::CNT<a> * self::CNT<(-1)> & a<=0 -> self::CNT<(-1)>;

lemma_prop "combine-CNT" self::CNT<a> * self::CNT<b> & a,b>=0 ->  self::CNT<a+b>;

// Lemma for error detection
lemma "ERR-RACE" self::LatchIn{- %P}<> * self::CNT<n> & n<0 -> emp & flow __Fail;

lemma "ERR-DEADLOCK" self::CNT<a> * self::CNT<b> & a>0 & b<0 -> emp & flow __Fail;

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
  requires emp 
  ensures emp & flow __norm; // failed
//ensures emp & flow __Fail; // ok
{
  cell p;
  CDL c = create_latch(2) with p'::cell<_>;
  par {p, c@L}
  {
    case {c@L} c'::LatchOut{+ p'::cell<_>}<> * c'::CNT<(0)> ->
      await(c);
      dprint;
    ||
    case {p, c@L} c'::LatchIn{- p'::cell<_>}<> * c'::CNT<(2)> ->
      p = new cell(1);
      countDown(c);
      dprint;
  }
  dprint;
}
