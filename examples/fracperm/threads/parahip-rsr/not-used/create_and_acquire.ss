/*
  Using predicates to handle unbounded number of locks.

  Note that this simplified example abstracts away
  the use of waitlevels.

 */

data node{
  lock l;
  node next;
} //data structure

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//heap predicates, n is size, S is the set of locks in the linked list
list<n,S> == self=null & n=0 & S={}
   or self::node<l,next> * l::LOCK<> * next::list<n-1,S1> & S = union(S1, {l})
  inv n>=0;

// create a linked list and acquire all of its locks
node create_and_acquire(int n)
  requires  n>=0
  ensures res::list<n,S> & LS'=union(LS,S); //'
{
  if (n==0){ return null;}
  else{
    lock l = new lock();
    //initialization
    init[LOCK](l);
    release(l);
    acquire(l);
    node tmp;
    tmp = create_and_acquire(n-1);
    return new node(l,tmp);
  }
}
