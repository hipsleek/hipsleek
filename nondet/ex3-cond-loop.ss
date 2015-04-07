pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

bool nondet_bool()
  requires true
  ensures res::nondet<>;

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
# nondet/ex3.ss

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)


*/
