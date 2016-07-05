relation nondet(int i).
relation nondetB(bool i).
  /* inv true; */

int nondeterm()
  requires true
  ensures nondet(res);

bool nondet_bool()
  requires true
  ensures nondetB(res);

void foo(bool b) 
 case {
  b -> requires Loop ensures false;
  !b -> requires Term[] ensures true;
 }
{ 
  //bool b = nondet_bool();
  // state |- b::nondet<> ~~> CondNonDet<>
  if (b) {
    foo(!b);
  }
  //dprint;
}

/*
# nondet/ex3.ss

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)

  LoopErr  |- 

 
*/
