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
data cell{
  int val;
}

data lock{
  int lck;
}

declare_lock LOCKA<x> == self::lock<_>
  inv x::cell<v> & v>=0;

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
