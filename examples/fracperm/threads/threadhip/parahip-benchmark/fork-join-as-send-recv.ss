/*
  An deadlock-free example that cannot be proven
  by either encoding fork/join as send/receive or
  assigning waitlevels to thread identifiers.

  We briefly explain why such an encoding is impossible
  in the end of this example.

  A simplified of this example is no-deadlock4.ss
 */

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<> * self::LOCK(f2)<> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<> * self::LOCK(f2)<> -> self::LOCK(f1+f2)<>;

void destroyLock(lock l)
  requires l::lock<>
  ensures emp;

void func(lock l1)
  requires l1::LOCK(0.6)<> & [waitlevel<l1.mu # l1 notin LS]
  ensures l1::LOCK(0.6)<> & LS'=LS;//'
{
  acquire(l1);
  release(l1);
}

void main()
  requires emp & LS={}
  ensures emp & LS'={}; //'
{
   lock l1 = new lock();
   init[LOCK](l1); //initialize l1 with invariant LOCK
   release(l1);

   lock l2 = new lock();
   init[LOCK](l2); //initialize l2 with invariant LOCK
   release(l2);

   thrd id1 = fork(func,l1);
   thrd id2 = fork(func,l2);

   acquire(l2);
   join(id1);
   release(l2);

   acquire(l1);
   join(id2);
   release(l1);

   //re-claim all resource
   acquire(l1);
   finalize(l1);
   destroyLock(l1);

   acquire(l2);
   finalize(l2);
   destroyLock(l2);

}

/*
There is a level associated with each lock and channel. There are 2 rules
for the translation: (1) when fork, the newly added channel should have
level less than all locklevels that the child thread is going to acquire 
and (2) threads have to acquire locks and receive on channel in an 
increasing order of levels.

The above program is translated as follows:

 main(){

  l1=new lock();
  l2=new lock();

  ch1 = new channel(); //ch1 to encoding fork/join of thread 1
  id1=fork(foo,l1,ch1); //level(ch1)<level(l1)

  ch2 = new channel(); //ch2 to encoding fork/join of thread 2
  id2=fork(foo,l2,ch2); //level(ch2)<level(l2)

  acquire(l2);
  receive ch1; //join(id1);// level(l2)<level(ch1)
  release(l2);

  acquire(l1);
  receive ch2; //join(id2);// level(l1)<level(ch2)
  release(l1);
 }

Although this example is DEADLOCK-FREE, it is rejected because it is
unclear how to find a proper waitlevel for ch1 and ch2, i.e.
level(ch1)<level(l1)<level(ch2)<level(l2)<level(ch1) leads to FALSE.

*/
