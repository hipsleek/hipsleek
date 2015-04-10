pred_prim nondet<>
  inv true;

bool nondet_bool()
  requires true
  ensures r::nondet<>;

void errorM()
  requires true
  ensures true & flow __Error;

void foo() 
  requires true
  ensures true & flow __ErrorND;
{ 
  bool b = nondet_bool();
  if (b) {
    errorM();
  }
  dprint;
}

void goo() 
  requires true
  ensures true & flow __ErrorND;
{ 
  bool b = nondet_bool();
  if (b) {
    dprint;
  }
  dprint;
}

/*
# nondet/ex7.ss

Why need to check against a throw list?

WARNING: ex11-err-spec.ss_10:10_10:29:the result type 
  __Error#E is not covered by the throw list[__norm#E]

To make --efa-exc

Checking procedure foo$... 
Proving precondition in method errorM$ Failed.
  (must) cause: must_err (__Error#E) LOCS: [17;18]



*/
