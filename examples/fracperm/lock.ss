/*
  Issues:

  - If we define invariant as a pred, we need to support fractional permission in the predicate definition.

  - init(p,args); //do not need to introduce new syntax such as init(p) with inv(p,args).

  - Can use view_data_name to decide type of the invariants. Differentiate between different kinds of predicate definitions (can be an invariant or a view) by [view_data_name,args].

  - x::LOCK<> is just a dummy node (to denote that x is lockable), therefore, a heap node with x::LOCK<> * x::cell<l,0> does not mean UNSAT. Note, in sleek, LOCK can only match with LOCK when searching for proofs.

  - When acquire(x), release(x) and finalize(x), what is a good way to find the corresponding Invariant??? 
  (Type of x only is not enough, we need a list of args as well. Is it fine if we search the entail state for x::LOCK<> to identify the list of args )

  - May not need field supports.

  - May I use --imm for my proof?
 */


data cell{
  int val;
}

data lock{
}

cellInv<> == self::cell<v> & v>=0
  inv true;


declare_lock LOCKA<x> == self::lock<>
  inv self::cellInv<>;

init(self) -->
   requires 




self::LOCKA<x> ==
  requires self::lock<v> 
  case { 
    v=lock   -> true
    v=unlock -> x::cellInv<>
  }


self::LOCKA<x> == 
  requires self::lock<v> 
  case { 
    v=lock   -> true
    v=unlock -> x::cellInv<>
  }



void main()
  requires true
  ensures true;
{
  cell x;
  lock l;
  //lock l = new lock();
  l = new lock(0);
  x = new cell(0);
  //x::cell<0> * l::lock<_> & MUST={}
  init[LOCKA](l,x); // init(x,args)
  //l::LOCKA<x> * x::cell<0> & MUST={l}
  release(l);
  //l::LOCKA<x> & MUST={}
  acquire(l);
  //l::LOCKA<x> * x::cellInv<> & MUST={l}
  finalize(l);
  //l::lock<_> *  x::cellInv<> & MUST={}
}


data Cell2{
  bool lck;
  int val;
}

cellInv2<> == self.val::<v> & v>=0
  inv true;

declare_lock
LOCKB<n> == self::node<_>
  inv self::cellInv2<>;

self::LOCKB<> == 

  lock(self) -->
    requires [n] self::LOCKB(f)<n> & not(self in MUST)
    ensures  self::LOCKB(f)<n> * self::cellInv2<> & MUST'=MUST+{self}//'
  unlock(self) -->
    requires self::LOCKB(f)<> * self::CellInv2<> & self in MUST
    ensures  self::LOCKB(f)<> & MUST'=MUST-{self} //'
  init(self) -->
    requires self.lck::<_> & self \notin MUST
    ensures self::LOCKB(1)<> & MUST'=MUST+{self}//'
  finalize(self) -->
    requires self::LOCKB(1)<> & self in MUST
    ensures self.lck::<_> & MUST'=MUST-{self}//'

data cell2{
  lock l;
  int val;
}

void main()
  requires true
  ensures true;
{

  cell2 x;
  lock l;
  x=new cell2(l,0);
  init(l);

  
  lock(x.l);
  
  sync(o);
  lock(o);

  cell2 l;
  l = new cell2(0,0);

  
  //l::Cell2<0,0> & MUST={}
  init(l) using l::LOCKB<>; // init(x,args)
  //l::LOCKB<> * l.Cell2.val<0> & MUST={l}
  release(l);
  //l::LOCKB<> & MUST={}
  acquire(l);
  //l::LOCKB<> * l::cellInv<> & MUST={l}
  finalize(l);
  //l.lck::<_> *  l::cellInv<> & MUST={}
}
