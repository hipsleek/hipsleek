/*
  [working example]

  This example is given in the paper:
  "Local Reasoning for Storable Locks and Threads [APLAS 2007]"
  It is intricate because fractional permissions 
  are used to flexibly to relate the total #threads "M" and 
  the counter "count" and the resource so that only
  the last thread accessing the resource can dispose
  the resource

 */

data PACKET{
  lock lock;
  int count;
  int dat;
}

lemma "splitLock" self::LOCK(f)<x,y> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<x,y> * self::LOCK(f2)<x,y> -> self::LOCK(f1+f2)<x,y>;

void delete(ref PACKET p) requires p::PACKET<> ensures p'=null;

void delLock(ref lock l) requires l::lock<> ensures l'=null;

global PACKET p;
global lock l;
global int M;

LOCK<p,M> == self::lock<>
  inv self!=null
  inv_lock p::PACKET<self,count,dat> & count = X & X=0 & X<M
  or p::PACKET<self,count,dat> * self::LOCK(X/M)<p,M> & count=X & M > X >= 1;


void initialize(/* ref lock l, ref PACKET p, ref int M */)
  requires LS={} & M=10
  ensures LS'={} & M'=M; //'
{
  //{true & LS={}}
  l = new lock();
  p = new PACKET(l,0,0);
  init[LOCK](l,p,M);
  release[LOCK](l,p,M);
}

void thread(/* ref lock l, ref PACKET p, ref int M */)
  requires l::LOCK(1/M)<p,M> & LS={} & M=10
  ensures LS'={} & M'=M; //'
{
  acquire[LOCK](l,p,M);
  // . . . processing data . . .
  p.count++;
  if (p.count == M){
    // . . . Finalizing data . . .
    finalize[LOCK](l,p,M);
    delLock(l); //added by our system
    delete(p);
    //{ emp }
  }else{
    release[LOCK](l,p,M); // {both branches entail the later case of the invariant}
  }
}



/* =========================================== */
/* EXPECTED PROOF OUTLINE */
/* =========================================== */

/*

void initialize()
  requires LS={} & M=10
  ensures LS'={} & M'=M; //'
{
  //{true & LS={}}
  l = new lock();
  p = new PACKET(l,0,0);
  //{p::PACKET<l,0,0> * l::lock<_> & LS={}}
  init[LOCK](l,p,M);
  //{l::LOCK<p,M> * p::PACKET<l,0,0> & LS={l}}
  release[LOCK](l,p,M);
  //{l::LOCK<p,M> LS={}}
}

void thread()
  requires l::LOCK(1/M)<p,M> & LS={} & M=10
  ensures LS'={} & M'=M; //'
{
  //{l::LOCK(1/M)<p,M> & LS={}}
  acquire[LOCK](l,p,M);
  //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = X & X=0 & X<M
  //   or l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> * l::LOCK(X/M)<p,M> & count=X & M > X >= 1 }
  // . . . processing data . . .
  p.count++;
  //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = X+1 & X=0 & X<M
  //   or l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> * l::LOCK(X/M)<p,M> & count=X+1 & M > X >= 1 }
  if (p.count == M){
    //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = X+1 & X=0 & X<M & count=M
    //   or l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> * l::LOCK(X/M)<p,M> & count=X+1 & M > X >= 1 & count=M}
    //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = X+1 & X=0 & X<M & count=M & M=10
    //   or l::LOCK()<p,M> * p::PACKET<l,count,data> & count=X+1 & M > X >= 1 & count=M & M=10}
    //{false
    //   or l::LOCK()<p,M> * p::PACKET<l,count,data> & count=X+1 & M > X >= 1 & count=M & M=10}
    //{l::LOCK()<p,M> * p::PACKET<l,count,data> & count=X+1 & M > X >= 1 & count=M & M=10}
    // . . . Finalizing data . . .
    finalize[LOCK](l,p,M);
    //{FAIL
    //   or l::lock() * p::PACKET<l,count,data> & count=X+1 & M > X >= 1 & count=M}
    //{ l::lock() * p::PACKET<l,count,data> & count=X+1 & M > X >= 1 & count=M}
    delLock(l); //added by our system
    delete(p);
    //{ emp }
  }else{
    //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = X+1 & X=0 & X<M & count!=M & M=10
    //   or l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> * l::LOCK(X/M)<p,M> & count=X+1 & M > X >= 1 & count=!M & M=10}
    //{l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> & count = 1 & X=1 & X<=M & count!=M & M=10
    //   or l::LOCK(1/M)<p,M> * p::PACKET<l,count,data> * l::LOCK(X/M)<p,M> & count=X+1 & M > X >= 1 & count=!M & M=10}
    release[LOCK](l,p,M); // {both branches entail the later case of the invariant}
	//{ emp } because the resource invariant occupies all permissions in order to entail the or branch
  }
  //{LS'={}}
}

*/
