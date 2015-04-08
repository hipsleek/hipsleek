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
    foo(i-1);
  }
}

/*
# nondet/ex2.ss

What are we really checking here?
Are we checking the reachability of Loop?
Can we convert it into an explicit sleek test
at the post-condition?

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)

*/
