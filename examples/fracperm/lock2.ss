/*
  Example of locks and threads
 */

data lbit{
}

data cell{
  lbit l;
  int val;
}

cellInv<> == self::cell<l,v> & v>=0
  inv true;


void thread(cell x)
  requires x::LOCK(0.5)<>
  ensures x::LOCK(0.5)<>;
{
  //x::LOCK(0.5)<> & MUST={}
  acquire(x);
  //x::LOCK(0.5)<> * x::cell<l,v> & v>=0 & MUST={b}
  x.val++;
  //x::LOCK(0.5)<> * x::cell<l,v1> & v>=0 & v1=v+1 & MUST={b}
  release(x);
  //x::LOCK(0.5)<> & MUST={}
}


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

  //.................

  int id;
  id = fork(thread,x);
  //x::LOCK(0.5)<> & id=id_1 & MUST={} and x::LOCK(0.5)<> & thread=id_1
  thread(x);
  //x::LOCK(0.5)<> & id=id_1 & MUST={} and x::LOCK(0.5)<> & thread=id_1
  join(id);
  //x::LOCK<> & MUST={}

  //.................
  
  //x::LOCK<> & MUST={}
  acquire(x);
  //x::LOCK<> * x::cell<l,v> & MUST={x}
  finalize(x);
  //x::cell<l,v> * l::lbit<> & MUST={x}
}
