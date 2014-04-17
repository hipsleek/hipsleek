/*
  example of deadlocks in the presence of disjunctive delayed formula
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

//fractional permission combining
lemma "combineLock" self::LOCK(f1)<> * self::LOCK(f2)<> -> self::LOCK(f1+f2)<>;

void destroyLock(lock l)
  requires l::lock<>
  ensures emp;

/**/

void func(bool b, lock l1,lock l2)
 case{
  b -> requires l1::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS] ensures l1::LOCK(0.6)<> & LS'=LS;
  !b -> requires l2::LOCK(0.6)<> & [waitlevel<l2.mu # l2 notin LS] ensures l2::LOCK(0.6)<> & LS'=LS;
 }
{
  int i;
  if (b){
    acquire(l1);
    release(l1);
  }else{
    acquire(l2);
    release(l2);
  }
}

void main()
  requires emp & LS={}
  ensures emp & LS'={}; //'
{
   lock l1 = new lock();
   init[LOCK](l1); //initialize l1 with invariant LOCK
   release(l1);
   //
   lock l2 = new lock();
   init[LOCK](l2);
   release(l2);
   bool b = false;
   //LS={}
   int id = fork(func,b,l1,l2);
   //DELAYED: l1 notin LS & b | l2 notin LS & !b

   //LS={}
   acquire(l2);
   //LS={l2} & !b

   join(id); //CHECK, error because LS={l2} & !b |/- (l1 notin LS & b | l2 notin LS & !b)

   release(l2);

   acquire(l1);
   finalize(l1);
   destroyLock(l1);

   acquire(l2);
   finalize(l2);
   destroyLock(l2);
}
