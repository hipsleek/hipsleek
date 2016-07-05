/*
  Resemble the program in Lst 1. of the paper
  Verifying Class Invariants in Concurrent Programs - FASE2014
 */

data cell{int val;}

data Point{
  cell x;
  cell y;
}

//define lock invariant with name LOCK and a list of args
LOCK<p> == self::lock<>
  inv self!=null
  inv_lock p::Point<x,y> * x::cell<v1> * y::cell<v2> & v1+v2>=0;
//describe protected shared heap

void move(Point p, lock l)
  requires l::LOCK(0.5)<p> & l notin LS
  ensures l::LOCK(0.5)<p> & LS'=LS; //'
{
  acquire(l);
  cell x1 = p.x;
  cell x2 = p.y;
  x1.val=x1.val+1;
  x2.val=x2.val-1;
  /* x2.val=x2.val-2; //this will break the invariant */
  release(l); //invariant v1+v2>=0 still holds here
}
