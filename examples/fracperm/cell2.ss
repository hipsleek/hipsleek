data Cell2{
  int lck;
  int val;
}

cellInv2<> == self::Cell2<#,v> & v>=0;
  inv true;

declare_lock LOCKB<> == self::Cell2<_,#> //this can cause init more than twice
  inv self::cellInv2<>;

-------------------------------------------------
  init[LOCKB](self) -->
    requires self::Cell2<_, # > //partial field
    ensures self::LOCKB(1)<>

  finalize(self) -->
    requires self::LOCKB(1)<>
    ensures self::Cell2<_,#>

  acquire(self) -->
    requires self::LOCKB(f)<n>
    ensures  self::LOCKB(f)<n> * self::cellInv2<>

  release(self) -->
    requires self::LOCKB(f)<> * self::CellInv2<>
    ensures  self::LOCKB(f)<>
-------------------------------------------------

void main()
  requires true
  ensures true;
{

  Cell2 l;
  l = new Cell2(0,0);
  //l::Cell2<0,0>
  init[LOCKB](l);
  //l::LOCKB<> * l::Cell2<#,0>
  release(l);
  //l::LOCKB<>
  acquire(l);
  //l::LOCKB<> * l::cellInv<>
  l.val++;
  finalize(l);
  //l.Cell2::<_,#> *  l::Cell2<#,v> & v>=0
}

=======================================
-------------------------------------------------
  init[LOCKA](self) -->
    requires self::lock<_ > //partial field
    ensures self::LOCKA(1)<>

  finalize(self) -->
    requires self::LOCKA(1)<>
    ensures self::lock<_>

  acquire(self) -->
    requires self::LOCKA(f)<n>
    ensures  self::LOCKA(f)<n> * self::cellInv<>

  release(self) -->
    requires self::LOCKA(f)<> * self::CellInv<>
    ensures  self::LOCKA(f)<>
-------------------------------------------------

data cell{
  int val;
}

data lock{
  int lck;
}

pred cellInv<> == x::cell<v> & v>=0
  inv self!=null;

pred LOCKA<x> == self::lock<_>
  inv self!=null
  inv_lock x::cellInv<>;

void main()
  requires true
  ensures true;
{
  cell x;
  lock l;
  l = new lock(0); //dummy
  x = new cell(0);
  //x::cell<0> * l::lock<_>
  init[LOCKA](l,x);
  //l::LOCKA<x> * x::cell<0>
  release(l);
  //l::LOCKA<x>
  acquire(l);
  //l::LOCKA<x> * x::cell<v> & v>=0
  finalize(l);
  //l::lock<_> *  x::cellInv<>
}
