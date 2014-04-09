/*

  Inspired by an example given in the paper:
  "Local Reasoning for Storable Locks and Threads" [APLAS 2007]

  Improve the example in APLAS2008 by allowing a pool of threads (implemented as a linked list) for dynamic thread creation.

  The program is verified as:
  - Functionally correct
  - Data-race-free
  - Deadlock-free
 */

data PACKET{
  lock lock;
  int count;
  int dat;
}

data threadNode{
  thrd v;
  threadNode next;
}

/* A list of threads, i.e. a thread pool */
threadPool<l,n,M> == self=null & n=0
  or self::threadNode<v,q> * q::threadPool<l,n-1,M> * v::thrd<# l notin LS & M>0 --> true #>
  inv n>=0;

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<x,y> & f=f1+f2 & f1>0.0  -> self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> & 0.0<f<=1.0;

//fractional permission combining
lemma "combineLock" self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> -> self::LOCK(f1+f2)<x,y>;

void delete(ref PACKET p) requires p::PACKET<_,_,_> ensures p'=null;

void delLock(ref lock l) requires l::lock<> ensures l'=null;

global PACKET p;
global lock l;
global int M;

//define lock invariant with name LOCK and a list of args consisting of p and M
LOCK<p,M> == self::lock<>
  inv self!=null
  inv_lock p::PACKET<self,count,dat> & count = X & X=0 & X<M
  or p::PACKET<self,count,dat> * self::LOCK(X/M)<p,M> & count=X & M > X >= 1;
//describe protected shared heap

void main()
  requires LS={}
  ensures LS'={}; //'
{
  PACKET p;
  lock l;
  int M=10;
  //{true & LS={}}
  l = new lock();
  p = new PACKET(l,0,0);
  init[LOCK](l,p,M); //initialize l with invariant LOCK and a list of args consisting of p and M
  release(l);
  //create a pool of threads
  threadNode tn = createThreads(l,p,M);
  // wait for all threads to finish
  joinThreads(tn,l,p,M);
 
}

void thread(lock l, PACKET p, int M)
  requires l::LOCK(1/M)<p,M> & [waitlevel<l.mu # l notin LS] & M>0 
  ensures LS'=LS; //'
{
  acquire(l);
  // . . . processing data . . .
  p.count++;
  if (p.count == M){
    // . . . Finalizing data . . .
    finalize(l);
    delLock(l); //added by our system
    delete(p);
    //{ emp }
  }else{
    release(l); // {both branches entail the later case of the invariant}
  }
}

threadNode createhelper(lock l, PACKET p, int n, int M)
  requires l::LOCK(f)<p,M> & f=n/M & M>=n & n>=0 & [waitlevel<l.mu # l notin LS]
  ensures res::threadPool<l,n,M> & LS'=LS; //'
{
  if (n<1){return null;}
  else{
    thrd t = fork(thread,l,p,M);
    threadNode q = createhelper(l,p,n-1,M);
    threadNode node = new threadNode(t,q);
    return node;
  }
}

//create a thread pool with M threads
// sharing read accesses to the lock l.
threadNode createThreads(lock l, PACKET p, int M)
  requires l::LOCK<p,M> & M>0 & [waitlevel<l.mu # l notin LS]
  ensures res::threadPool<l,M,M> & LS'=LS; //'
{
  return createhelper(l,p,M,M);
}

void destroyThreadNode(threadNode x)
  requires x::threadNode<_,_>
  ensures true;

void joinhelper(threadNode tn, lock l, PACKET p, int n, int M)
  requires tn::threadPool<l,n,M> & M>=n & n>=0 & [waitlevel<l.mu # l notin LS]
  ensures true & LS'=LS; //'
{
  if (tn==null){return;}
  else{
    threadNode node = tn.next;
    joinhelper(node,l,p,n-1,M);
    thrd t = tn.v;
    join(t);
    destroyThreadNode(tn);
  }
}

// Join all threads in the thread pool
void joinThreads(threadNode tn, lock l, PACKET p, int M)
  requires tn::threadPool<l,M,M> & M>0 & [waitlevel<l.mu # l notin LS]
  ensures true  & LS'=LS; //'
{
  joinhelper(tn,l,p,M,M);
}
