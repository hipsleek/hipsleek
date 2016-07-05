pred_prim nondet<>
  inv true;

bool nondet_bool()
  requires true
  ensures r::nondet<>;

void foo() 
  requires LoopND
  ensures true;
{ 
  bool b = nondet_bool();
  if (b) {
    foo();
  }
  dprint;
}

/*
# nondet/ex7.ss

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)


*/
