pred_prim nondet<>
  inv true;

bool nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires LoopErr ensures emp;
  }
{ 
  bool b = nondetermB(); // b'::nondet<>
  bool d = i>=0 && b;   // d'= i'>=0 && b'
  if (d) {
    foo(i-1);
    dprint;
  }
}

/*
# nondet/ex6-nd-term.ss

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures emp;
    i >=0 -> requires LoopErr ensures emp;
  }
{ 
  bool b = nondetermB(); // b'::nondet<>
  bool d = i>=0 && b;   // d'= i'>=0 && b'
  if (d) {
    foo(i-1);
    dprint;
  }
}

Above spec would fail, as d' is not NONDET.
This is so, as i>=0 is DET. If i>=0 had been false,
the conditional becomes deterministically FALSE.
Hence, the conditional here is not non-deterministic.

*/
