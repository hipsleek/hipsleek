/*
  [working example]
  testVar(): lock protecting a variable (need vperm)
  testCell(): lock protecting a memory cell

// Still need MAY/MUST to be sound
-------------------------------------------------
  init[LOCKA](self) -->
    requires self::lock<_ >
    ensures [ref ls] self::LOCKA(1)<> & ls'=union(S,{self})

  finalize[LOCKA](self) -->
    requires self::LOCKA(1)<> & (self in ls) 
    ensures [ref ls] self::lock<_> & ls'=diff(ls,{self})

  acquire(self) -->
    requires [f] self::LOCKA(f)<n> & (self notin ls)
    ensures  [ref ls] self::LOCKA(f)<n> * self::cellInv<> & ls'=union(ls,{self})

  release(self) -->
    requires self::CellInv<> & (self in ls) & 0<f<=1
    ensures  [ref ls] ls'=diff(ls,{self})
-------------------------------------------------

*/


data cell{
  int val;
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
  requires LS={}
  ensures LS'={}; //'
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
  release(l);
  //l::LOCKA<x>
  //x=x+1; //FAIL due to not @full[x]

  assert LS'={}; //OK'

  acquire(l);
  //l::LOCKA<x> * x>=0
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
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKB](l,x);
  //l::LOCKB<x> * x::cell<0>
  x.val = x.val + 1;
  release(l);

  assert LS'={}; //OK'

  //l::LOCKB<x>
  acquire(l);
  //l::LOCKB<x> * x::cell<v> & v>=0
  //x.val = x.val - 1; //FAIL the invariant
  release(l);

  assert LS'={}; //OK'

  //l::LOCKB<x>
  acquire(l);
  //l::LOCKB<x> * x::cell<v> & v>=0
  finalize(l);
  //l::lock<> *  x::cellInv<>
}
