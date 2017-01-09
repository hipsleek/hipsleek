pred_prim nondet<>
  inv true;

int nondet_int()
  requires true
  ensures res::nondet<>;

bool nondet_bool()
  requires true
  ensures res::nondet<>;

void foo(int x) 
  requires Loop//ND
  ensures true;
{ 
  bool b = nondet_bool();
  int x = nondet_int();
  if (b) {
    foo(x);
  }
  dprint;
}

/*
# nondet/ex9.ss

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)


*/
