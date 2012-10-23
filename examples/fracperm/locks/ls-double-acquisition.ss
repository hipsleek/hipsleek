/*
  example of deadlocks due to double acquisition in sequential settings
 */

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

void func(lock l1)
  requires l1::LOCK<> & l1 notin LS & waitlevel<l1.mu
  ensures l1::LOCK<> & LS'=LS;//'
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
   acquire[LOCK](l1);
   //LS={l1}

   func(l1); //ERROR, double acquisition

   release[LOCK](l1);

   dprint;
}

