/*
  Fine-grained locking
 */

data lock{}

data cell{
  lock l;
  int val;
}

LOCK<x> == self::lock<>
  inv self!=null
  inv_lock (exists v: x::cell<self,v> & v>=0);

void main()
  requires true
  ensures true;
{
  lock l = new lock();
  cell x = new cell(l,0);
  init[LOCK](l,x);
  release[LOCK](l,x);

  //acquire[LOCK](l,x);
  test_acquire(l,x);
  finalize[LOCK](l,x);
}

//valid
void test_acquire(lock l,cell x)
  requires l::LOCK<x>
  ensures l::LOCK<x> * x::cell<l,v> & v>=0;
{
  acquire[LOCK](l,x);
}
