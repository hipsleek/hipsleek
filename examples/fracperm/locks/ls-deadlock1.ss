/*
  example of deadlocks due to interractions of fork/join
  and acquire/release
*/

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
  requires l1::LOCK(0.6)<> & l1 notin LS
  ensures l1::LOCK(0.6)<> & LS'=LS;//'
{
  acquire[LOCK](l1);
  release[LOCK](l1);
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
   lock l1 = new lock();
   //initialization
   init[LOCK](l1);
   release[LOCK](l1);
   //
   int id = fork(func,l1); //DELAYED
   /* acquire[LOCK](l1); */
   /* release[LOCK](l1); */
   acquire[LOCK](l1);
   join(id); // CHECK, Delayed checking failure
   release[LOCK](l1);
   dprint;
}
