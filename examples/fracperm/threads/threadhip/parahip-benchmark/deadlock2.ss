/*
  example of deadlocks due to interractions of fork/join
  and acquire/release
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<> * self::LOCK(f2)<> -> self::LOCK(f1+f2)<>;

void destroyLock(lock l)
  requires l::lock<>
  ensures emp;

void func(lock l1)
  requires l1::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.6)<> & LS'=LS;//'
{
  acquire(l1);
  release(l1);
}

void main()
  requires emp & LS={}
  ensures emp & LS'={}; //'
{
   lock l1 = new lock();
   //initialization
   init[LOCK](l1);
   release(l1);
   //
   acquire(l1);
   thrd id = fork(func,l1); //DELAYED
   join(id); // CHECK, Delayed checking failure
   release(l1);

   acquire(l1);
   finalize(l1);
   destroyLock(l1);
}
