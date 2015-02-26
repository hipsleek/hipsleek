/*
  General usage
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

void func(lock l1)
  requires l1::LOCK<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK<> & LS'=LS & waitlevel'=waitlevel;//'
{
  acquire(l1);
  release(l1);
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
  lock l1 = new lock();//l1.mu>0 by default
  //initialization
  init[LOCK](l1);//initialize l1 with invariant LOCK
  release(l1); //release after establising lock invariant
  //
  acquire(l1);//mutual exclusion
  release(l1);
  //
  func(l1); //procedure call
  //finalization
  acquire(l1);
  finalize(l1);
}
