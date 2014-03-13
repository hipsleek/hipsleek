/*
  [working example]

Output:

Procedure test$ result FAIL-1
Procedure test2$ result FAIL-1
Procedure test3$ result FAIL-1
Procedure test4$ result FAIL-1

*/

data cell{
  int val;
}

//cellInv<> == self::cell<v> & v>=0
//  inv self!=null;

LOCKA<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<v> & v>=0);
  //inv_lock x::cellInv<>;

//finalize w/o init or acquire => FAIL
void test()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>

  finalize(l); // fail
  /* finalize[LOCKA](l,x); // fail */
  //fail because l is not in locked state
  //LOCKA <> lock

}

//release w/o acquire or finalize -> FAIL
void test2()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>

  release(l); //FAIL
  /* release[LOCKA](l,x); //FAIL */
  //fail because l is not in locked state
  //LOCKA <> lock

}

//acquiring twice 
// w/o LOCKSET --> SUCCESS due to false ctx 
// w LOCKSET --> FAIL
void test3()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  //dprint;
  release(l);
  //l::LOCKA<x>
  acquire(l);
  acquire(l); 
  // w/o LOCKSET: still SUCESS
  //acquire invariant twice => false context in the presence of heap

  // w LOCKSET: FAIL
  // because LS is already in LOCKSET (non-reentrant locks)

}

//release twice => FAIL due to 2 reasons
// (1) fail to entail the invariant
// (2) not holding the lock -> cannot release 
void test4()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>

  release(l);

  //l::LOCKA<x>
  /* dprint; */

  release(l); //FAIL
}
