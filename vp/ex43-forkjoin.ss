/*
  General usage
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting for concurrency
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
     requires l1::LOCK(0.5)<> & [waitlevel<l1.mu # l1 notin LS]
     ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  //acquire(l1);
  release(l1);
}

/*
void main()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level); //define a locklevel
  //initialization
  init[LOCK](l1);
  release(l1);
  //
  thrd id = fork(func,l1); //create a chile thread
  //DELAY
  //
  acquire(l1);
  release(l1);
  //
  join(id);//checking ok
}
*/
