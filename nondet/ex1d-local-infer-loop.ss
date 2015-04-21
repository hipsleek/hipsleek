pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires Loop ensures true;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    //assume i'>=0;
    infer_assume [i];
    foo(i);
  }
}

/*

# nondet/ex1d-loop.ss

infer_assume[i'] will attempt to infer a
pre-condition that can be assumed on i'
to allow the verification to succeed.

It should also print the inferred 
local (non-deterministic) condition.

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires Loop ensures true;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    //assume i'>=0;
    infer_assume[i'];
    foo(i);
  }
}

*/
