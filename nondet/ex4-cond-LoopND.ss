pred_prim nondet<>
inv true;
/* relation nondetB(bool i). */
  /* inv true; */

/* int nondeterm() */
/*   requires true */
/*   ensures nondet(res); */

bool nondet_bool()
  requires true
  ensures res::nondet<>;

void foo() 
  requires LoopND
  ensures emp;
{ 
  bool b = nondet_bool();
  // state |- b::nondet<> ~~> CondNonDet<>
  if (b) {
    foo();
  }
  dprint;
}

/*
# nondet/ex4.ss

 Can we change to LoopND?

 Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)

*/
