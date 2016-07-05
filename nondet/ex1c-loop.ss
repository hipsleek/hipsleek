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
    assume i'>=0;
    foo(i);
  }
}

/*

# nondet/ex1a-loop.ss
Adding true in post led to the following..

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)

There is no sleek checking here.
Can we convert this into a sleek proof!

*/
