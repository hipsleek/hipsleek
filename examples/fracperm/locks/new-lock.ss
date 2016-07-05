/*
  Example of creating new locks inside a procedure
 */

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

void test()
  requires true
  ensures LS'=LS; //'
{

  int level;
  assume level'>waitlevel';
  lock l1 = new lock(level);

  init[LOCK](l1); //initialize l1 with invariant LOCK
  release(l1);

  acquire(l1);
  release(l1);

  acquire(l1);
  finalize(l1);
}

void test2()
  requires true
  ensures LS'=LS; //'
{

  int level1;
  assume level1'>waitlevel';
  lock l1 = new lock(level1);

  int level2;
  assume level2'>level1';
  lock l2 = new lock(level2);

  init[LOCK](l1); //initialize l1 with invariant LOCK
  release(l1);

  init[LOCK](l2); //initialize l1 with invariant LOCK
  release(l2);

  acquire(l1);
  acquire(l2);
  release(l2);
  release(l1);

}
