/*

  Inspired by an example given in the paper:
  "Local Reasoning for Storable Locks and Threads" [APLAS 2007]

 */

data PACKET{
  lock lock;
  int count;
  int dat;
}

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<x,y> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> & 0.0<f<=1.0;

//fractional permission combining
lemma "combineLock" self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> -> self::LOCK(f1+f2)<x,y>;

void delete(ref PACKET p) requires p::PACKET<> ensures p'=null;

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

void initialize(/* ref lock l, ref PACKET p, ref int M */)
  requires LS={} & M=10
  ensures LS'={} & M'=M; //'
{
  //{true & LS={}}
  l = new lock();
  p = new PACKET(l,0,0);
  init[LOCK](l,p,M); //initialize l with invariant LOCK and a list of args consisting of p and M
  release(l);
}

void thread(/* ref lock l, ref PACKET p, ref int M */)
  requires l::LOCK(1/M)<p,M> & [waitlevel<l.mu # l notin LS] & M=10 
  ensures LS'=LS & M'=M; //'
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
