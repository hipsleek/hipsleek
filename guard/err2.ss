data cell {
  int val;
}

HeapPred H(cell a).
HeapPred G(cell a).

int foo(cell p)
  infer [H,G]
  requires H(p)
  ensures G(p);
{
    int i = p.val;
    goo(p);
    return i;
}

void goo(cell p)
  requires p=null
  ensures true;

/*
# err2.ss : 

  Should we perhaps infer a false here?
  Inferring false may be too strong.

Context of Verification Failure: 1 File "err2.ss",Line:11,Col:10
Last Proving Location: 1 File "err2.ss",Line:14,Col:4

Procedure foo$cell FAIL.(2)

Exception Failure("Proving precond failed") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure foo$cell
Stop Omega... 34 invocations 
0 false contexts at: ()

*/
