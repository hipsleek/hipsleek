pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires MayLoop ensures true;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    foo(i);
  }
}

/*
# nondet/ex1b.ss

MayLoop is OK but not precise.

*/
