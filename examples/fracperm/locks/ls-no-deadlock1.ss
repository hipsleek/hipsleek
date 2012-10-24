/*
  An example of deadlock-free programs but may not be
  not provable by related work
 */

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
  requires l1::LOCK(0.6)<> & l1 notin LS & waitlevel<l1.mu
  ensures l1::LOCK(0.6)<> & LS'=LS;//'
{
  acquire(l1);
  release(l1);
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
   lock l1 = new lock();
   init[LOCK](l1);
   release(l1);
   acquire(l1);
   int id = fork(func,l1);
   release(l1);
   join(id);
   
}
