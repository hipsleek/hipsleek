/*
  Example of failed synchronization when using CountDownLatch

 */

//CountDownLatch
//CountDownLatch
class CDL extends Object {}

/* data CDL{ */
/* } */

data cell{
  int v;
}

//Thread: initial state 
pred_prim THRD{(-)P,(+)Q}<c1:CDL,c2:CDL,g:WAIT>;

//Thread: forked state
pred_prim THRD2{(+)Q@Split}<c1:CDL,c2:CDL,g:WAIT>;

//Thread: dead state
pred_prim DEAD<>;

pred_prim LatchIn{(-)P}<>;

pred_prim LatchOut{(+)P}<>;

pred_prim CNT<n:int>;



lemma_split "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine1" self::CNT<a> * self::CNT<b> & a>=0 & b>=0 -> self::CNT<a+b>;

lemma "combine2" self::CNT<a> * self::CNT<b> & a<=0 & b<=0 -> self::CNT<a+b>;

lemma "normalize" self::LatchOut{%P}<> * self::CNT<n> & n<0 -> %P;

lemma "error1" self::CNT<a> * self::CNT<b> & a>0 & b<0 ->  emp & flow __Fail;

lemma "error2" self::LatchIn{%P}<> * self::CNT<n> & n<0 ->  emp & flow __Fail;


lemma_split "wait-split" self::WAIT(f)<S> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::WAIT(f1)<S> * self::WAIT(f2)<S> & 0.0<f<=1.0;

lemma "wait-combine" self::WAIT(f1)<S1> * self::WAIT(f2)<S2> -> self::WAIT(f1+f2)<S> & S=union(S1,S2);

//synchronization lemma
lemma_prop "wait-for" c1::CNT<a> * c2::CNT<b> * x::WAIT(f)<S> & a>0 & b<0 & v notin S & v=tup2(c2,c1)->  c1::CNT<a> * c2::CNT<b> * x::WAIT(f)<S1> & S1=union(S,{tup2(c2,c1)}) & a>0 & b<0;

//normalization of dead threads
lemma "thrd_normalize" self::THRD2{%Q}<c1,c2,g> * self::DEAD<> -> %Q;


/********************************************/
/********************************************/

//wait-for graph
global WAIT g; //ghost

/********************************************/
/****************THREADS*********************/
thrd create_thrd() // with %P
  requires true
  ensures (exists c1,c2,g,S: res::THRD{g::WAIT<S>@S1 * c1::LatchOut{emp}<> * c1::CNT<0> * c2::LatchIn{emp}<> * c2::CNT<1> & S={} & c1!=c2, g::WAIT<S1> * c1::CNT<(-1)> * c2::CNT<0> & S1={tup2(c1,c2)} }<c1,c2,g>);

void fork_thrd(thrd t,CDL c1,CDL c2,WAIT g)
  requires t::THRD{%P,%Q}<c1,c2,g> * %P
  ensures  t::THRD2{%Q}<c1,c2,g>;

void join_thrd(thrd t, CDL c1,CDL c2,WAIT g)
  requires t::THRD2{%Q}<c1,c2,g>
  ensures  t::DEAD<> * %Q;
  requires t::DEAD<>
  ensures  t::DEAD<>;

/********************************************/
/****************LATCHES*********************/
CDL create_latch(int n) // with %P
  requires n>0
  ensures (exists x: res::LatchIn{emp}<> * res::LatchOut{emp}<> * res::CNT<n>);

void countDown(CDL c)
  requires c::LatchIn{%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<n> & n<=0
  ensures c::CNT<n>;

void await(CDL c)
  requires c::LatchOut{%P}<> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
  requires c::CNT<n> & n<0
  ensures c::CNT<n>;

/********************************************/

void thread1(CDL c1, CDL c2, WAIT g)
  requires g::WAIT<S> * c1::LatchOut{emp}<> * c1::CNT<0> * c2::LatchIn{emp}<> * c2::CNT<1> & S={} & c1!=c2 
  ensures g::WAIT<S1> * c1::CNT<(-1)> * c2::CNT<0> & S1={tup2(c1,c2)};
{
  await(c1);
  countDown(c2);
}


void main(ref WAIT g)
  requires g::WAIT<S> & S={} ensures true;
{
  CDL c1 = create_latch(1);
  CDL c2 = create_latch(1);
  assume c1'!=c2';

  thrd tid =  create_thrd(); //create thread1

  //thread1(c1,c2,g);

  fork_thrd(tid,c1,c2,g);

  dprint;

  await(c2);
  countDown(c1);

  dprint;

  join_thrd(tid,c1,c2,g); //ERROR, since c::CNT<1> * c::CNT<-1>

  dprint;
}

