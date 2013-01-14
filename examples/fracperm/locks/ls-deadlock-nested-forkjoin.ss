/*
  A deadlocked example in the presence of nested fork/join.

  A deadlock occurs when main waits at join(id1), thread1 waits
  at join(id2), and thread2 waits at acquire(l2);
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting for concurrency
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void thread2(lock l2)
     requires l2::LOCK(0.6)<> & [waitlevel<l2.mu # l2 notin LS]
     ensures l2::LOCK(0.6)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  acquire(l2);
  release(l2);
}

void thread1(lock l1, lock l2)
     requires l1::LOCK(0.6)<> * l2::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS & l2 notin LS]
     ensures l1::LOCK(0.6)<> * l2::LOCK(0.6)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  int id2 = fork(thread2,l2);
  acquire(l1);
  release(l1);
  join(id2);
  //release(l1);//release here also results in deadlock
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
  lock l1 = new lock(); //define a locklevel
  //initialization
  init[LOCK](l1);
  release(l1);
  //
  lock l2 = new lock(); //define a locklevel
  init[LOCK](l2);
  release(l2);
  //
  int id1 = fork(thread1,l1,l2); //create a chile thread
  //DELAY
  //
  acquire(l2);
  join(id1);// CHECKING --> error because LS={l2}
  release(l2);
}
