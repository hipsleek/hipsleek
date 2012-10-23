/*
  [working example]

  This example implements the motivating example in
  Aquinas's paper [ESOP'08].

  However, there is a critical modification:
  1. The original example is not correct due to the 
  use of incorrect permissions (50% and 50%). Aquinas's
  thesis uses distinguished permissions and therefore
  avoid this issue.

  2. We, however, show that it is sufficient to just change 
  the permissions to 40% and 60%.

  Note: we use exceptions to model return and break inside a loop

*/


data cell{
  lock lck;
  int val1;
  int val2;
  int val3;
}

class rexc extends __Exc{} //exception when return from a loop

class bexc extends __Exc{} //exception when break from a loop

LOCK<x> == /* self::cell<self,v1,v2,v3> & v1=v2 */ self::lock<>
  inv self!=null
  inv_lock x::cell<self,v1,v2,v3> & v1=v2 & v3=1
  or x::cell<self,v1,v2,v3> * self::LOCK(0.6)<x> & v1=v2 & v3=0;
  //inv_lock x::cellInv<>;

lemma "splitLock" self::LOCK(f)<x> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x> * self::LOCK(f2)<x> & 0.0<f<=1.0;

lemma "combineLock" self::LOCK(f1)<x> * self::LOCK(f2)<x> -> self::LOCK(f1+f2)<x>;

//LOCK protecting a cell
void main()
  requires LS={}
  ensures true; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(l,0,0,0);
  int i=0;
  init[LOCK](l,x);
  /* dprint; */
  x.val1=1;
  x.val2=1;
  int id;
  id = fork(thread,l,x);
  dprint;
  x.val3=1;

  try{

  while (true)
    requires l::LOCK(0.4)<x> * x::cell<l,v1,v2,v3> & v1=v2 & v3=1 & l in LS & waitlevel=l.mu & l.mu>0
          or l::LOCK(1.0)<x> * x::cell<l,v1,v2,v3> & v1=v2 & v3=0 & l in LS & waitlevel=l.mu & l.mu>0 // 0.4 + 0.6 = 1.0'
    ensures l'::LOCK(1.0)<x> * x'::cell<self,v11,v22,v33> & l'=l & v11=v22 & v33=0 & LS'=LS & waitlevel'=waitlevel & flow bexc;//'
  {
    if (x.val3==0){
      raise new bexc(); // break
    };
    x.val1=i;
    x.val2=i;
    release[LOCK](l,x);
    /* dprint; */
    i=i+1;
    acquire[LOCK](l,x);
  } //end TRY
  }catch(bexc e){
      ; //no-op
  };
  finalize[LOCK](l,x);
}

void thread(lock l, cell x)
  requires l::LOCK(0.6)<x> & l notin LS & waitlevel<l.mu
  ensures LS'=LS; //'
{
  try{
    //syntatic sugar
    while(true)
      requires l::LOCK(0.6)<x> & l notin LS & waitlevel<l.mu
      ensures LS'=LS & flow rexc; //'
    {
      dprint;
      acquire[LOCK](l,x);
      dprint;
      x.val1=x.val1 + x.val1;
      x.val2=x.val2 + x.val2;
      dprint;
      if (x.val1>10) {
        x.val3=0;
        release[LOCK](l,x);
        raise new rexc(); //return;
      }
      release[LOCK](l,x);
    };
    // End Try
  }catch (rexc e){
    ; //no-op
  };
  return;
}
