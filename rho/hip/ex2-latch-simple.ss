/*
  Example with simple CountDownLatch
 */

//CountDownLatch
data CDL{
}

data cell{
  int v;
}

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;
pred_prim CNT<n:int>
inv n>=(-1);

//lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

/********************************************/
CDL create_latch(int n) // with %P
  requires n>0
  ensures (exists x: res::LatchIn{-x::cell<10>}<> * res::LatchOut{+x::cell<10>}<> * res::CNT<n>);

void countDown(CDL c)
  requires c::LatchIn{-%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<(-1)> 
  ensures c::CNT<(-1)>;

void await(CDL c)
  requires c::LatchOut{+%P}<> * c::CNT<0>
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
  countDown(c);


  await(c);

  //assert x'::cell<10>;

  //destroyCell(x);
}

/*
# latch.ss
Proving precondition in method countDown$CDL Failed.
Empty list_failesc_context

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "latch.ss",Line:52,Col:2

Procedure main$ FAIL.(2)

Exception Failure("Proving precond failed") Occurred!

Error(s) detected when checking procedure main$
Stop Omega... 52 invocations 

// why below fail?

id: 3; caller: []; line: 52; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail (exists x_1563,v_int_50_1423': x_41'::cell<v_int_48_1561> * 
c_42'::LatchIn{ - (exists flted_26_67: x_1563::cell<flted_26_67>&flted_26_67=10&
{FLOW,(4,5)=__norm#E})[]}<> * 
c_42'::LatchOut{ + (exists flted_26_68: x_1563::cell<flted_26_68>&flted_26_68=10&
{FLOW,(4,5)=__norm#E})[]}<> * 
c_42'::CNT{}<v_int_50_1423'>&v_int_48_1561=10 & v_int_50_1423'=1&
{FLOW,(4,5)=__norm#E})[]
 |-  c_42'::LatchIn{ - HVar P&{FLOW,(4,5)=__norm#E}[]}<> * (HVar P) * 
c_42'::CNT{}<n>&0<n&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  failctx
         
          fe_kind: MAY
          fe_name: separation entailment

*/
