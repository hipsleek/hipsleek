/*
  example of deadlocks due to double acquisition in sequential settings
 */

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

void func(lock l1)
  requires l1::LOCK<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK<> & LS'=LS;//'
{
  acquire(l1);
  release(l1);
}

void main()
  requires LS={}
  ensures LS'={}; //'
{
   lock l1 = new lock();
   //initialization
   init[LOCK](l1);//initialize l1 with invariant LOCK
   release(l1);
   //
   acquire(l1);
   //LS={l1}

   func(l1); //ERROR, double acquisition

   release(l1);

   
}

