/*
  Example of failed synchronization when using CountDownLatch

 */

//CountDownLatch
data CDL{
}

data cell{
  int v;
}

//Thread: initial state 
pred_prim THRD{(-)P,(+)Q}<c:CDL>
inv c!=null;

//Thread: forked state
pred_prim THRD2{(+)Q@Split}<c:CDL>
inv c!=null;

//Thread: dead state
pred_prim DEAD<>;

pred_prim LatchIn{(-)P}<>;

pred_prim LatchOut{(+)P}<>;

pred_prim CNT<n:int>;

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine1" self::CNT<a> * self::CNT<b> & a>=0 & b>=0 -> self::CNT<a+b>;

lemma "combine2" self::CNT<a> * self::CNT<b> & a<=0 & b<=0 -> self::CNT<a+b>;

lemma "normalize" self::LatchOut{%P}<> * self::CNT<n> & n<0 -> %P;

lemma "error1" self::CNT<a> * self::CNT<b> & a>0 & b<0 ->  emp & flow __Fail;

lemma "error2" self::LatchIn{%P}<> * self::CNT<n> & n<0 ->  emp & flow __Fail;

//synchronization lemma
//lemma_prop "wait-for" c1::CNT<a> * c2::CNT<b> * x::WAIT<S> & a>0 & b<0 & v notin S & v=tup2(c1,c2)->  c1::CNT<a> * c2::CNT<b> * x::WAIT<S1> & S1=union(S,{tup2(c1,c2)}) & a>0 & b<0.

//normalization of dead threads
lemma "thrd_normalize" self::THRD2{%Q}<c> * self::DEAD<> -> %Q;

/********************************************/
/****************THREADS*********************/
thrd create_thrd() // with %P
  requires true
  ensures (exists c: res::THRD{c::LatchOut{emp}<> * c::CNT<0> & true, c::CNT<(-1)>}<c>);

void fork_thrd(thrd t,CDL c)
  requires t::THRD{%P,%Q}<c> * %P
  ensures  t::THRD2{%Q}<c>;

void join_thrd(thrd t)
  requires exists c: t::THRD2{%Q}<c>
  ensures  t::DEAD<> * %Q;

/********************************************/
/****************LATCHES*********************/
CDL create_latch(int n) // with %P
  requires n>0
  ensures (exists x: res::LatchIn{emp}<> * res::LatchOut{emp}<> * res::CNT<n>);

void countDown(CDL c)
  requires c::LatchIn{%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;

void await(CDL c)
  requires c::LatchOut{%P}<> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
/********************************************/

void thread1(CDL c)
  requires c::LatchOut{emp}<> * c::CNT<0>
  ensures  c::CNT<(-1)>;
{
  await(c);
}


void main()
  requires emp ensures emp ;
{
  CDL c = create_latch(2);

  thrd tid =  create_thrd(); //create thread1

  fork_thrd(tid,c);

  countDown(c);

  join_thrd(tid); //ERROR, since c::CNT<1> * c::CNT<-1>

}

