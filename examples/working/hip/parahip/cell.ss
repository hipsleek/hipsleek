/*
  [working example]

// need MAY/MUST LOCKSET to be sound
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

LOCKB<x,y> == self::lock<>
  inv self!=null
  inv_lock (exists v1,v2: x::cell<v1> * y::cell<v2> & v1+v2>=2);

//valid
// a lock protecting 1 location
void test()
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
  /* dprint; */
  release(l);
  //l::LOCKA<x>
  acquire(l);
  //l::LOCKA<x> * x::cell<v> & v>=0
  finalize(l);
  //l::lock<> *  x::cellInv<>
}

//fail
// a lock protecting 2 location
void test1()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  cell y;
  lock l;
  l = new lock(); //dummy
  x = new cell(1);
  y = new cell(1);
  init[LOCKB](l,x,y); // lock l protext x and y
  /* dprint; */
  x.val--;
  /* dprint; */
  release(l); //can not, invariant not hold
  /* dprint; */
  //finalize
  acquire(l);
  finalize(l);
}

