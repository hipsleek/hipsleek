/*
  An example of deadlock-free programs: locks
  are acquired in a strictly increasing order.
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1, lock l2)
  requires l1::LOCK(0.6)<> * l2::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS & l2 notin LS] & l1!=l2 & l1.mu < l2.mu
  ensures l1::LOCK(0.6)<> * l2::LOCK(0.6)<> & LS'=LS;//'
{
  acquire(l1);
  acquire(l2);
  release(l1);
  release(l2);
}

void main()
  requires LS={}
  ensures LS={};
{
  lock l1 = new lock(1);
  init[LOCK](l1); //initialize l1 with invariant LOCK
  release(l1);
  //
  lock l2 = new lock(2);
  init[LOCK](l2);
  release(l2);
  //
  assume(l1'!=l2'); //TODO: this should be inferred automatically based on fractional permissions
  
  //
  int id = fork(func,l1,l2); //DELAYED
  
  //
  acquire(l1);
  acquire(l2);
  release(l1);
  release(l2);
  
  //
  join(id); // CHECK, ok
  
}
