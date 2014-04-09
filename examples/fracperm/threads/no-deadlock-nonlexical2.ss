/*
  A deadlock-free example in the presence of
  Non-lexical Fork/join Concurrency, First-class Threads and Locks, and Multi-join
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting for concurrency
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<> * self::LOCK(f2)<> -> self::LOCK(f1+f2)<>;

void destroyLock(lock l)
     requires l::LOCK<>
     ensures true;

void thread1(lock l)
     requires l::LOCK(0.5)<> & [waitlevel<l.mu # l notin LS]
     ensures l::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  acquire(l);
  release(l);
}

void thread2(lock l, thrd t1)
  requires t1::thrd<# l notin LS' --> l::LOCK(0.25)<> & true #> & l notin LS
  ensures l::LOCK(0.25)<> & LS'=LS & waitlevel'=waitlevel; //'
{
  join(t1); // CHECKING --> OK
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
  thrd t1 = fork(thread1,l); //create the thread1 thread
  //DELAY
  //
  acquire(l);
  //
  thrd t2 = fork(thread2,l,t1); // pass in the thread1 thread
  //
  release(l);
  //
  //Without joining t1, destroyLock will fail
  join(t1);// CHECKING --> OK
  //
  join(t2);// CHECKING --> OK
  //
  destroyLock(l);
}
