/*
  General usage
*/

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;//describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  acquire(l1);
  release(l1);
}

void func_acquire(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & waitlevel<waitlevel';//'
{
  acquire(l1);
}

void func_release(lock l1)
  requires l1::LOCK(0.5)<> & [waitlevel=l1.mu # l1 in LS]
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & waitlevel'<waitlevel;//'
{
  release(l1);
}

//test initialization and finalization
void f1()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  init[LOCK](l1);
  release(l1);
  //
  acquire(l1);
  release(l1);
  //finalization
  acquire(l1);
  finalize(l1);
}

//test sequential procedure calls
void f2()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  init[LOCK](l1);
  release(l1);
  //sequential call
  func(l1);

  //
  acquire(l1);
  release(l1);
}

//test fork/join
void f3()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  init[LOCK](l1);
  release(l1);
  //
  int id = fork(func,l1);
  //
  acquire(l1);
  release(l1);
  //
  join(id);
}

//test non-lexical acquire/release
void f4()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);

  //initialization
  init[LOCK](l1);
  release(l1);
  //
  func_acquire(l1);
  //
  func_release(l1);
  //
  func_acquire(l1);
  //
  func_release(l1);
  //
  acquire(l1);
  release(l1);
  //
}

//test fork/join and non-lexical acquire/release
void f5()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  init[LOCK](l1);
  release(l1);
  //
  int id = fork(func,l1);
  //
  func_acquire(l1);
  //
  func_release(l1);
  //
  join(id);
  //
  acquire(l1);
  release(l1);
}

