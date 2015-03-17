/*
  Additional test for waitlevel: operator >,  >= , <=
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func2(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'>=waitlevel;//'
{
  acquire(l1);
  release(l1);
  dprint;
}

void func3(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'<=waitlevel;//'
{
  acquire(l1);
  release(l1);
  dprint;
}

void func4(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel>=l1.mu # l1 in LS]
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1});//'
{
  release(l1);
  dprint;
}
