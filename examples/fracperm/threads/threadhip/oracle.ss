/*

  Inspired by a motivating example in the paper
  "Oracle semantics for concurrent separation logic" [ESOP'08].

*/


data cell{
  lock lck;
  int val1;
  int val2;
  int val3;
}

class rexc extends __Exc{} //exception when return from a loop

class bexc extends __Exc{} //exception when break from a loop

//define lock invariant with name LOCK protecting a cell x
LOCK<x> == /* self::cell<self,v1,v2,v3> & v1=v2 */ self::lock<>
  inv self!=null
  inv_lock x::cell<self,v1,v2,v3> & v1=v2 & v3=1
  or x::cell<self,v1,v2,v3> * self::LOCK(0.6)<x> & v1=v2 & v3=0;
  //inv_lock x::cellInv<>;
//describe protected shared heap

//fractional permission splitting
lemma "splitLock" self::LOCK(f)<x> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x> * self::LOCK(f2)<x> & 0.0<f<=1.0;

//fractional permission combining
lemma "combineLock" self::LOCK(f1)<x> * self::LOCK(f2)<x> -> self::LOCK(f1+f2)<x>;

void destroylock(lock l)
  requires l::lock<>
  ensures emp;

void destroyCell(cell x)
  requires x::cell<_,_,_,_>
  ensures emp;

void destroyBexc(bexc e)
  requires e::bexc<>
  ensures emp;

void destroyRexc(rexc e)
  requires e::rexc<>
  ensures emp;

//LOCK protecting a cell
void main()
  requires emp & LS={}
  ensures emp & LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(l,0,0,0);
  int i=0;
  init[LOCK](l,x); //initialize l with invariant LOCK and

  x.val1=1;
  x.val2=1;
  thrd id;
  id = fork(thread,l,x);
  x.val3=1;

  try{

  while (true)
    requires l::LOCK(0.4)<x> * x::cell<l,v1,v2,v3> & [waitlevel=l.mu # l in LS] & v1=v2 & v3=1
          or l::LOCK(1.0)<x> * x::cell<l,v1,v2,v3> & [waitlevel=l.mu # l in LS] & v1=v2 & v3=0 // 0.4 + 0.6 = 1.0'
    ensures l'::LOCK(1.0)<x> * x'::cell<self,v11,v22,v33> * eres::bexc<> & l'=l & v11=v22 & v33=0 & LS'=LS & waitlevel'=waitlevel & flow bexc;//'
  {
    if (x.val3==0){
      raise new bexc(); // break
    };
    x.val1=i;
    x.val2=i;
    release(l);
    i=i+1;
    acquire(l);
  } //end TRY

  }catch(bexc e){
    destroyBexc(e);
  };
  finalize(l);

  destroylock(l);
  destroyCell(x);

  join(id); //to prevent thread leakage,
  //otherwise has to specify in post-condition

}

void thread(lock l, cell x)
  requires l::LOCK(0.6)<x> & [waitlevel<l.mu # l notin LS]
  ensures LS'=LS; //'
{
  try{

    //syntatic sugar
    while(true)
      requires l::LOCK(0.6)<x> & [waitlevel<l.mu # l notin LS ]
        ensures eres::rexc<> & LS'=LS & flow rexc; //'
    {
      acquire(l);
      x.val1=x.val1 + x.val1;
      x.val2=x.val2 + x.val2;
      if (x.val1>10) {
        x.val3=0;
        release(l);
        raise new rexc(); //return;
      }
      release(l);
    };
    // End Try

  }catch (rexc e){
    destroyRexc(e);
  };

  return;
}
