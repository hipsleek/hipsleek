data cell {
  int val;
}

bool rand()
  requires true
  ensures !res or res;

void free(cell x)
 requires x::cell<_>
 ensures emp;

int foo()
  requires true
  ensures true;
{
  cell x;
  x=new cell(5);
  int r=x.val;
  free(x);
  //dprint;
  free(x);
  return r;
}

/*
# ex3-double-free.ss

Why is this called a bind-failure?
I guess we should only call it a bind failure for
field access x.field failure.

For pre-condition, maybe just use "pre-cond failure
or unmatched node failure?

Procedure foo$ FAIL.(2)
Exception Failure("bind failure exception") Occurred!



*/
