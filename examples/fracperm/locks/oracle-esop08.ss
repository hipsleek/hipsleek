/*
  [nonworking example]
  [Bug] - required distinguished fractional permissions

  This example tried to implement the motivating example in
  Aquinas's paper [ESOP'08].

  However, it is non-working because the paper requires
  the notion of distinguished fractional permissions to 
  distiguished bw left and right halves of a share.

  Specifcally, (1) the invariant holds a left-permission
  when v3=0, and (2) the main thread holds a right half 
  and the child thread holds a left half; therefore, only
  the main thread can join the lef-half permission in the
  invariant to form a full permission and later finalize
  the lock.

  In case of normal fractional permissions, the child thread
  which holds a half of permission can also acquire another
  half from the invariant and therefore breaks the semantics
  of the program/invariant.

*/


data cell{
  lock lck;
  int val1;
  int val2;
  int val3;
}

data lock{
}

//cellInv<> == self::cell<v> & v>=0
//  inv self!=null;

LOCK<x> == /* self::cell<self,v1,v2,v3> & v1=v2 */ self::lock<>
  inv self!=null
  inv_lock x::cell<self,v1,v2,v3> & v1=v2 & v3=1
  or x::cell<self,v1,v2,v3> * self::LOCK(1/2)<x> & v1=v2 & v3=0;
  //inv_lock x::cellInv<>;

lemma "splitLock" self::LOCK(f)<x> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::LOCK(f1)<x> * self::LOCK(f2)<x> & 0.0<f<=1.0;

                                                                 lemma "combineLock" self::LOCK(f1)<x> * self::LOCK(f2)<x> -> self::LOCK(f1+f2)<x>;

//LOCK protecting a cell
/* void main() */
/*   requires ls={} */
/*   ensures ls'={}; //' */
/* { */
/*   cell x; */
/*   lock l; */
/*   l = new lock(); //dummy */
/*   x = new cell(l,0,0,0); */

/*   init[LOCK](l,x); */
/*   /\* dprint; *\/ */
/*   x.val1=1; */
/*   x.val2=1; */
/*   x.val3=1; */
/*   /\* dprint; *\/ */
/*   release[LOCK](l,x); // val3 = 1 => no need to SPLIT */
/*                       // va3 = 0 => no to SPLIT */
/*   /\* dprint; *\/ */

/*   int id; */
/*   id = fork(thread,l,x); // ??? consider drop ls,ls' when fork/join */
/*   dprint; */

/*   acquire[LOCK](l,x); */
/*   dprint; */

/*   while (true) */
/*     requires l::LOCK(1/2)<x> * x::cell<l,v1,v2,v3> & v1=v2 & v3=1 & ls={l} */
/*           or l::LOCK(1.0)<x> * x::cell<l,v1,v2,v3> & v1=v2 & v3=0 & ls={l} // 1/2 + 1/2 = 1.0 */
/*     ensures l::LOCK(1/2)<x> * x::cell<l,v1,v2,v3> & v1=v2 & v3=1 & ls={l} */
/*     or l::LOCK(1/2)<x> * x::cell<self,v1,v2,v3> * l::LOCK(1/2)<x> & v1=v2 & v3=0 & ls={l}; */
/*   { */

/*     /\* dprint; *\/ */
/*     x.val1=1; */
/*     x.val2=1; */
/*     /\* x.val3=2; *\/ */
/*     /\* dprint; *\/ */
/*     release[LOCK](l,x); */

/*     acquire[LOCK](l,x); */
/*     /\* dprint; *\/ */
/*   } */

/*   release[LOCK](l,x); */
/*   /\* dprint; *\/ */

/* } */

/* void thread2(lock l, cell x) */
/*   requires l::LOCK(1/2)<x> & @value[l,x] & ls={} */
/*   ensures l::LOCK(1/2)<x> & ls'={}; //' */
/* { */
/*   dprint; */
/*   while(true) */
/*   requires l::LOCK(1/2)<x> & ls={} */
/*   ensures l::LOCK(1/2)<x> & ls'={}; //' */
/*   { */
/*     acquire[LOCK](l,x); */
/*     dprint; */
/*     x.val1=1; */
/*     x.val2=1; */
/*     x.val3=1; */
/*     dprint; */
/*     release[LOCK](l,x); // should allow a split here */
/*     dprint; */
/*   } */
/*   dprint; */
/* } */

void thread(lock l, cell x)
  requires l::LOCK(1/2)<x> & @value[l,x] & ls={}
  ensures l::LOCK(1/2)<x> & ls'={}; //'
{
  dprint;
  acquire[LOCK](l,x);
  dprint;
  /* x.val1=1; */
  /* x.val2=1; */
  /* x.val3=0;  */
  if (x.val1>10) {
    x.val3=0;
    release[LOCK](l,x); // should allow a split here
    return;
  }
  else{
  /*   dprint; */
  // val3 = 0, this should FAIL because
  //   delta1 * 1/2 * val3=0 or delta1 * 1.0 * val3=0
  //   fail to ENTAIL
  //   delta1 * 1/2 * val3=1 or delta1 * 1.0 * val3=0

  // val1 = 1, this will be VALID because
  //   delta1 * 1/2 * val3=1 or delta1 * 1.0 * val3=1
  //   was able to ENTAIL
  //   delta1 * 1/2 * val3=1 or delta1 * 1.0 * val3=0
    release[LOCK](l,x); // should allow a split here
    dprint;
  }
}
