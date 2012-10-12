/*
  example of deadlocks due to interractions of fork/join
  and acquire/release
*/

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
     requires l1::LOCK(0.5)<> & l1 in ls
     ensures l1::LOCK(0.5)<> & ls'=ls;//'
{
  acquire[LOCK](l1);
  release[LOCK](l1);
}

void main()
  requires ls={}
  ensures ls={};
{
   lock l1 = new lock();
   init[LOCK](l1);
   release[LOCK](l1);
   dprint;
   //acquire[LOCK](l1);
   int id = fork(func,l1);
   dprint;
   acquire[LOCK](l1);
   release[LOCK](l1);
   dprint;
   join(id);
   dprint;
   //release[LOCK](l1);
   dprint;

}
