/*
  Test waitlevel
*/

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
  requires l1::LOCK(0.5)<> & l1 notin LS & l1.mu>0 & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  /* dprint; */
  acquire[LOCK](l1);
  release[LOCK](l1);
  /* dprint; */
}

void func_test(int x, int y)
 requires x>y 
  ensures true;
{
  ;
}

void func_empty2()
  requires true
  ensures LS'=LS & waitlevel'=waitlevel;//'
{
  ;
}

void func_empty(lock l1)
  requires l1::LOCK(0.5)<>  & l1 notin LS /*& l1.mu>0 & waitlevel<l1.mu */
  ensures l1::LOCK(0.5)<> &LS'=LS & waitlevel'=waitlevel;//'
{
  ;
}

void func_acquire(lock l1)
  requires l1::LOCK(0.5)<> & l1 notin LS & l1.mu>0 & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & waitlevel<waitlevel';//'
{
  acquire[LOCK](l1);
}

//FAIL
void func_acquire_fail1(lock l1)
  requires l1::LOCK(0.5)<> & l1 notin LS & l1.mu>0 & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & waitlevel=waitlevel';//'
{
  acquire[LOCK](l1);
}

//FAIL
void func_acquire_fail2(lock l1)
  requires l1::LOCK(0.5)<> & l1 notin LS & l1.mu>0 & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & waitlevel>waitlevel';//'
{
  acquire[LOCK](l1);
}

void func_release(lock l1)
  requires l1::LOCK(0.5)<> & l1 in LS & l1.mu>0 & waitlevel=l1.mu
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & waitlevel'<waitlevel;//'
{
  release[LOCK](l1);
}

//FAIL
void func_release_fail1(lock l1)
  requires l1::LOCK(0.5)<> & l1 in LS & l1.mu>0 & waitlevel=l1.mu
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & waitlevel'=waitlevel;//'
{
  release[LOCK](l1);
}

//FAIL
void func_release_fail2(lock l1)
  requires l1::LOCK(0.5)<> & l1 in LS & l1.mu>0 & waitlevel=l1.mu
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & waitlevel'>waitlevel;//'
{
  release[LOCK](l1);
}

void func_release_acquire(lock l1)
  requires l1::LOCK(0.5)<> & l1 in LS & l1.mu>0 & waitlevel=l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'=waitlevel;//'
{
  release[LOCK](l1);
  acquire[LOCK](l1);
}

//FAIL
void func_release_acquire_fail(lock l1)
  requires l1::LOCK(0.5)<> & l1 in LS & l1.mu>0 & waitlevel=l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & waitlevel'<waitlevel;//'
{
  release[LOCK](l1);
  acquire[LOCK](l1);
}

//test initialization and finalization
void f1()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  dprint;
  //initialization
  init[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
  acquire[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //finalization
  acquire[LOCK](l1);
  finalize[LOCK](l1);
  dprint;
}

//test sequential procedure calls
void f2()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  dprint;
  init[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //sequential call
  func(l1);

  //
  acquire[LOCK](l1);
  release[LOCK](l1);

  dprint;
}

//test fork/join
void f3()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  //initialization
  dprint;
  init[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
  int id = fork(func,l1);
  dprint;
  //
  acquire[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
  join(id);
  dprint;
}

//test non-lexical acquire/release
void f4()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  dprint;
  //initialization
  init[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
  func_acquire(l1);
  dprint;
  //
  func_release(l1);
  dprint;
  //
  func_acquire(l1);
  dprint;
  //
  func_release(l1);
  dprint;
  //
  acquire[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
}

//test fork/join and non-lexical acquire/release
void f5()
  requires LS={}
  ensures LS'={}; //'
{
  int level = 100;
  lock l1 = new lock(level);
  dprint;
  //initialization
  init[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
  int id = fork(func,l1);
  dprint;
  //
  func_acquire(l1);
  dprint;
  //
  func_release(l1);
  dprint;
  //
  join(id);
  dprint;
  //
  acquire[LOCK](l1);
  release[LOCK](l1);
  dprint;
  //
}

