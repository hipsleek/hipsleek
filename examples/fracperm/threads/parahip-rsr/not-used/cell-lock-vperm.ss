/*
  [working example]
  testVar(): lock protecting a variable (need vperm)
  testCell(): lock protecting a memory cell

  Output:
Procedure testCell$ SUCCESS
Procedure testVar$ result FAIL-1

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

//cellInv<> == self::cell<v> & v>=0
//  inv self!=null;

LOCKA<x> == self::lock<>
  inv self!=null
  inv_lock (@full[x] & x>=1);
  //inv_lock x::cellInv<>;

LOCKB<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<v> & v>=1);
  //inv_lock x::cellInv<>;

//lock protecting a variable
//FAIL
void testVar()
  requires LS={}
  ensures LS'={}; //'
{
  int x;
  lock l;
  l = new lock(); //dummy
  x = 1;
  //x'=1 * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x'=1
  //x++;
  x--; //fail due to the invariant
  release(l);
  //l::LOCKA<x>

  //x=x+1; //FAIL due to not @full[x]

  acquire(l);
  //l::LOCKA<x> * x>=1
  x++;
  finalize(l);
  //l::lock<>

}

//LOCK protecting a cell
void testCell()
  requires LS={}
  ensures LS'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(1);
  //x::cell<1> * l::lock<>
  init[LOCKB](l,x);
  //l::LOCKB<x> * x::cell<1>

  x.val = x.val + 1;

  release(l);


  //l::LOCKB<x>
  acquire(l);
  //l::LOCKB<x> * x::cell<v> & v>=1
  //x.val = x.val - 1; //FAIL the invariant
  release(l);


  //l::LOCKB<x>
  acquire(l);
  //l::LOCKB<x> * x::cell<v> & v>=1
  finalize(l);
  //l::lock<> *  x::cellInv<>

}
