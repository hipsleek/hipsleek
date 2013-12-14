/*
  General usage
*/

LOCK<> == self::lock<>
  inv self!=null
  inv_lock true;

lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

void func(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & v=l1.mu & v notin LSMU & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & LSMU'=LSMU & waitlevel'=waitlevel;//'
{
  acquire(l1);
  release(l1);
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
  requires exists v: l1::LOCK(0.5)<>  & l1 notin LS & v=l1.mu & v notin LSMU
  ensures l1::LOCK(0.5)<> &LS'=LS & waitlevel'=waitlevel & LSMU'=LSMU;//'
{
  ;
}

void func_acquire(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & waitlevel<l1.mu & v=l1.mu & v notin LSMU
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & LSMU'=union(LSMU,{l1.mu}) & waitlevel<waitlevel';//'
{
  acquire(l1);
}

//FAIL
void func_acquire_fail1(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & waitlevel<l1.mu & v=l1.mu & v notin LSMU
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & LSMU'=union(LSMU,{l1.mu}) & waitlevel=waitlevel';//'
{
  acquire(l1);
}

//FAIL
void func_acquire_fail2(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & waitlevel<l1.mu & v=l1.mu & v notin LSMU
  ensures l1::LOCK(0.5)<> & LS'=union(LS,{l1}) & LSMU'=union(LSMU,{l1.mu}) & waitlevel>waitlevel';//'
{
  acquire(l1);
}

void func_release(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU /* & l1.mu>0 */
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & LSMU'=diff(LSMU,{l1.mu}) & waitlevel'<waitlevel;//'
{
  release(l1);
}

//FAIL
void func_release_fail1(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU /* & l1.mu>0 */
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & LSMU'=diff(LSMU,{l1.mu}) & waitlevel'=waitlevel;//'
{
  release(l1);
}

//FAIL
void func_release_fail2(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU /* & l1.mu>0 */
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & LSMU'=diff(LSMU,{l1.mu}) & waitlevel'>waitlevel;//'
{
  release(l1);
}

void func_release_acquire(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU
  ensures l1::LOCK(0.5)<> & LS'=LS  & LSMU'=LSMU & waitlevel'=waitlevel;//'
{
  release(l1);
  acquire(l1);
}

void func_release_acquire_while(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU
  ensures l1::LOCK(0.5)<> & LS'=LS  & LSMU'=LSMU & waitlevel'=waitlevel;//'
{
  while(true)
    requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU
    ensures l1::LOCK(0.5)<> & LS'=LS  & LSMU'=LSMU & waitlevel'=waitlevel;//'
  {
    release(l1);
    acquire(l1);
  }
}

//FAIL
void func_release_acquire_fail(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 in LS & waitlevel=l1.mu & v=l1.mu & v in LSMU
  ensures l1::LOCK(0.5)<> & LS'=LS  & LSMU'=LSMU & waitlevel'<waitlevel;//'
{
  release(l1);
  acquire(l1);
}

//test initialization and finalization
void f1()
  requires LS={} & LSMU={}
  ensures LS'={} & LSMU'={}; //'
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
  requires LS={} & LSMU={}
  ensures LS'={} & LSMU'={}; //'
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
  requires LS={} & LSMU={}
  ensures LS'={} & LSMU'={}; //'
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
  requires LS={} & LSMU={}
  ensures LS'={} & LSMU'={}; //'
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
  dprint;
  //
  acquire(l1);
  release(l1);
  
  //
}

//test fork/join and non-lexical acquire/release
void f5()
  requires LS={} & LSMU={}
  ensures LS'={} & LSMU'={}; //'
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
  
  //
}

void func2(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & v=l1.mu & v notin LSMU & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & LSMU'=LSMU & waitlevel'>=waitlevel;//'
{
  acquire(l1);
  release(l1);
}

void func3(lock l1)
  requires exists v: l1::LOCK(0.5)<> & l1 notin LS & v=l1.mu & v notin LSMU & waitlevel<l1.mu
  ensures l1::LOCK(0.5)<> & LS'=LS & LSMU'=LSMU & waitlevel'<=waitlevel;//'
{
  acquire(l1);
  release(l1);
}

void func4(lock l1)
  requires exists v: l1::LOCK(0.5)<> & [waitlevel>=l1.mu # l1 in LS] & l1.mu=v & v in LSMU
  ensures l1::LOCK(0.5)<> & LS'=diff(LS,{l1}) & LSMU'=diff(LSMU,{l1.mu});//'
{
  release(l1);
}
