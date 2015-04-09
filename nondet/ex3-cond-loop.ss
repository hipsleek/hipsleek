relation nondet(int i).
relation nondetB(bool i).
  /* inv true; */

int nondeterm()
  requires true
  ensures nondet(res);

bool nondet_bool()
  requires true
  ensures nondetB(res);

void foo() 
  requires Loop
  ensures true;
{ 
  bool b = nondet_bool();
  if (b) {
    foo();
  }
  dprint;
}

/*
# nondet/ex3.ss

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)


*/
