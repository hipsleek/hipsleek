/*
  How to lock GLOBAL stack variables?

  IMPORTANT: For concurrency, we may be unsound
  consider global variables as pass-by-ref!

  If we want to concurrently read from a shared variable 
      => pass it by value
  If we want to concurrently write to a shared variable 
      => lock it (with @full in the invariant)

  Assume:
  - In a method:
    + @full for all local vars
    + @zero for all global vars
*/

///////////////////////////////////////////////
/// Owicky-Gries: Using auxiliary variables ///
///////////////////////////////////////////////

global int x;
global int y,z;
global lock l;
//invariant
inv(l) := @full(x,y,z) & x=y+z

void inc1()
  requires y=0;
  ensures y'=1; //'
{
  // at this point, we might assume that
  // we have @zero for all global vars
  acquire(l);
  //{@full(x,y,z) & x=y+z & y=0}
  x=x+1;
  y=1;
  //{@full(x,y,z) & x+1=y+z & y=1}
  release(l);
}

void inc2()
  requires z=0
  ensures z'=1; //'
{
  acquire(l);
  //{@full(x,y,z) & x=y+z & z=0}
  x=x+1;
  z=1;
  //{@full(x,y,z) & x+1=y+z & z=1}
  release(l);
}

//each of a parent thread and a child thread increases x by 1
//y,z is to count the increment of x
void main()
  requires true
  ensures true;
{
  int id;
  x=0;
  y=0;z=0;
  id = fork(inc1); // this will create new thread to increase x by 1
  inc2();
  join(id);
  //we need to ensure
  assert y'=1;
  assert z'=1;
  assert x'=2; //'
}






///////////////////////////////////////////////
/// Without auxiliary variables             ///
///////////////////////////////////////////////

// don't know how to prove
global int x;
global lock l;


//do we need to annotate VarPerm for global vars???
//concurrent, have not added global vars into forked method
//How to say, x is shared???
//How to defind the invariant for the lock l
void inc()
  requires true
  ensures true; //' not sure how to write the spec without ghost var
{
  //because x is shared, we have to lock it for safety
  acquire(l); //can we have something like requires and ensures
  x=x+1;
  release(l);
}

void main()
  requires true
  ensures true;
{
  int id;
  x=0;
  id = fork(inc); // this will create new thread to increase x by 1
  inc();
  join(id);
  assert x'=x+2; //expected'
}
