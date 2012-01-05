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

data lbit{
}

data cell{
  lbit l;
  int val;
}

cellInv<> == self::cell<l,v>
  inv true;

void main()
  requires true
  ensures true;
{
  cell x;
  lock l = new lock();
  x = new cell(l,0);
  //x::cell<l,0> * l::lbit<> & MUST={}
  init(x); // init(x,args)
  //x::LOCK<> * x::cell<l,0> & MUST={x}
  release(x);
  //x::LOCK<> & MUST={}
  acquire(x);
  //x::LOCK<> * x::cell<l,v> & MUST={x}
  finalize(x);
  //x::cell<l,v> * l::lbit<> & MUST={x}
}
