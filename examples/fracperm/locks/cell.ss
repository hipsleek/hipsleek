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

LOCKB<x,y> == self::lock<>
  inv self!=null
  inv_lock (exists v1,v2: x::cell<v1> * y::cell<v2> & v1+v2>=0);

//valid
// a lock protecting 1 location
void main()
  requires ls={}
  ensures ls'={}; //'
{
  cell x;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  dprint;
  release[LOCKA](l,x);
  //l::LOCKA<x>
  acquire[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<v> & v>=0
  finalize[LOCKA](l,x);
  //l::lock<> *  x::cellInv<>
}

//fail
// a lock protecting 2 location
void main1()
  requires ls={}
  ensures ls'={}; //'
{
  cell x;
  cell y;
  lock l;
  l = new lock(); //dummy
  x = new cell(0);
  y = new cell(0);
  init[LOCKB](l,x,y); // lock l protext x and y
  dprint;
  x.val--;
  dprint;
  release[LOCKB](l,x,y); //can not, invariant not hold
  dprint;
  //finalize
  acquire[LOCKB](l,x,y);
  finalize[LOCKB](l,x,y);
}

