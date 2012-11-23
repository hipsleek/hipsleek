/*
  Example of locks, threads and inter-procedural fork/join
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


int testfork(cell x)
  requires x::LOCK(0.5)<>
  ensures res=z
          and x::LOCK(0.5)<> & thread=z
{
  int id;
  //x::LOCK(0.5)<> & MUST={}
  id = fork(thread,x);
  //id = id_1 & MUST={} and x::LOCK(0.5) & thread=id_1
  return id;
}

void testjoin(cell x, int id)
  requires x::LOCK(0.5)<> & id=id_1 
           and x::LOCK(0.5)<> & thread=id_1
  ensures x::LOCK<>
{
  join(id);
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
  //x::LOCK<> & MUST={}
  id = testfork(x);
  //x::LOCK(0.5)<> & id=id_1 & MUST={} and x::LOCK(0.5)<> & thread=id_1
  thread(x);
  //x::LOCK(0.5)<> & id=id_1 & MUST={} and x::LOCK(0.5)<> & thread=id_1
  testjoin(x,id);
  //x::LOCK<> & MUST={}

  //.................
  
  //x::LOCK<> & MUST={}
  acquire(x);
  //x::LOCK<> * x::cell<l,v> & MUST={x}
  finalize(x);
  //x::cell<l,v> * l::lbit<> & MUST={x}
}
