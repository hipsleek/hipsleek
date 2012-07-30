/*
  [working example]
  testVar(): lock protecting a variable (need vperm)
  testCell(): lock protecting a memory cell

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

*/

/*

Example with VPERM
-------------------------------------------------
  init[LOCKA](l,x) -->
    requires l::lock<_ >
    ensures l::LOCKA<x>

  finalize[LOCKA](l,x) -->
    requires l::LOCKA(x)<>
    ensures l::lock<_>

  acquire[LOCKA](l,x) -->
    requires [f] ::LOCKA(f)<x>
    ensures  l::LOCKA(f)<x> * @full[x] & x'>=0

  release[LOCKA](l,x) -->
    requires l::LOCKA(f)<x> * @full[x] & x'>=0
    ensures  l::LOCKA(f)<x> // or x' ??? // LOCKA is redundant
-------------------------------------------------

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
  inv_lock (@full[x] & x>=0);
  //inv_lock x::cellInv<>;

LOCKB<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<v> & v>=0);
  //inv_lock x::cellInv<>;

//lock protecting a variable
void testVar()
  requires true
  ensures true;
{
  int x;
  lock l;
  l = new lock(); //dummy
  x = 0;
  //x'=0 * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x'=0
  x++;
  //x--; //fail due to the invariant
  release[LOCKA](l,x);
  //l::LOCKA<x>

  //x=x+1; //FAIL due to not @full[x]

  acquire[LOCKA](l,x);
  //l::LOCKA<x> * x>=0
  x++;
  finalize[LOCKA](l,x);
  //l::lock<>
  dprint;
}

//LOCK protecting a cell
void testCell()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKB](l,x);
  //l::LOCKB<x> * x::cell<0>
  dprint;
  x.val = x.val + 1;
  dprint;
  release[LOCKB](l,x);

  dprint;

  //l::LOCKB<x>
  acquire[LOCKB](l,x);
  //l::LOCKB<x> * x::cell<v> & v>=0
  //x.val = x.val - 1; //FAIL the invariant
  release[LOCKB](l,x);


  //l::LOCKB<x>
  acquire[LOCKB](l,x);
  //l::LOCKB<x> * x::cell<v> & v>=0
  finalize[LOCKB](l,x);
  //l::lock<> *  x::cellInv<>
  dprint;
}
