relation nondet(int i).
relation nondetB(int i).
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
}

/*
# nondet/err3.ss

type-error but verification still proceeded.
is this OK?



*/
