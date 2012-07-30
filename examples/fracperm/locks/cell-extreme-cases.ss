/*
  [working example]

// Still need MAY/MUST to be sound
-------------------------------------------------
  init[LOCKA](self) -->
    requires self::lock<_ >
    ensures self::LOCKA(1)<>

  finalize[LOCKA](self) -->
    requires self::LOCKA(1)<>
    ensures self::lock<_>

  acquire(self) -->
    requires [f] self::LOCKA(f)<n>
    ensures  self::LOCKA(f)<n> * self::cellInv<>

  release(self) -->
    requires self::LOCKA(f)<> * self::CellInv<>
    ensures  self::LOCKA(f)<>
-------------------------------------------------

Output:

Procedure test$ result FAIL-1
Procedure test2$ result FAIL-1
Procedure test3$ SUCCESS
Procedure test4$ result FAIL-1

*/

data cell{
  int val;
}

data lock{
}

//cellInv<> == self::cell<v> & v>=0
//  inv self!=null;

LOCKA<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<v> & v>=0);
  //inv_lock x::cellInv<>;

//finalize w/o init or acquire => FAIL
void test()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  //init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  //dprint;
  //release[LOCKA](l,x);
  //l::LOCKA<x>
  //acquire[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<v> & v>=0
  dprint;
  finalize[LOCKA](l,x); //fail
  dprint;
  //l::lock<> *  x::cellInv<>
}

//release w/o acquire or finalize -> FAIL
void test2()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  //init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  //dprint;
  release[LOCKA](l,x); //FAIL
  //l::LOCKA<x>
  //acquire[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<v> & v>=0
  //dprint;
  //finalize[LOCKA](l,x); //fail
  //dprint;
  //l::lock<> *  x::cellInv<>
}

//acquiring twice -> false context -> success
void test3()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  //dprint;
  release[LOCKA](l,x);
  //l::LOCKA<x>
  acquire[LOCKA](l,x);
  acquire[LOCKA](l,x); //still SUCESS
  //acquire invariant twice => false context in the presence of heap
  //dprint;
  //l::LOCKA<x> * x::cell<v> & v>=0
  //dprint;
  //finalize[LOCKA](l,x); //fail
  //dprint;
  //l::lock<> *  x::cellInv<>
}

//release twice => fail to entail the invariant -> FAIL
void test4()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  //dprint;
  release[LOCKA](l,x);
  release[LOCKA](l,x); //FAIL
  dprint;
}
