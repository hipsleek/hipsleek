/*
  A deadlocked example in the presence of non-lexical fork/join.

  In response to reviewers of CAV2013.

*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting for concurrency
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<> * self::LOCK(f2)<> -> self::LOCK(f1+f2)<>;

void foo(lock l)
     requires l::LOCK(0.5)<> & [waitlevel<l.mu # l notin LS]
     ensures l::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  acquire(l);
  release(l);
}

void bar(lock l, int tid1)
     requires l::LOCK(0.3)<> & l notin LS
              and thread=tid1 & l notin LS --> l::LOCK(0.5)<>
     ensures l::LOCK(0.8)<> & LS'=LS;//'
{
  join(tid1);
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
  lock l = new lock(); //define a locklevel
  //initialization
  init[LOCK](l);
  release(l);
  //
  int tid1 = fork(foo,l); //create the foo thread
  //DELAY
  //
  int tid2 = fork(bar,l,tid1); // pass in the foo thread
  //
  acquire(l);
  //
  join(tid2);// CHECKING --> FAIL
  release(l);
}
