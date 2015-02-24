/*
  In this example, we disable the use of waitlevel
 */

data node{
  lock l;
  node next;
} //data structure

//define lock invariant with name LOCK and empty list of args
LOCK<> == self::lock<>
  inv self!=null
  inv_lock true; //describe protected shared heap

//heap predicates
list<n,S> == self=null & n=0 & S={}
   or self::node<l,next> * l::LOCK<> * next::list<n-1,S1> & S = union(S1, {l})
  inv n>=0;

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
