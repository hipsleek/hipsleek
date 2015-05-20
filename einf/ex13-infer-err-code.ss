relation P(int x).

void foo(int x)
  infer [P,@err_must]
  requires P(x)
  ensures true & flow __flow;
{
   assert x'>0 assume true;
}


/*
# ex13.ss



assert:ex13-infer-err-code.ss:8: 3:  : ok


Context of Verification Failure: _0:0_0:0

Last Proving Location: ex13-infer-err-code.ss_8:3_8:26

ERROR: at _0:0_0:0
Message: heap_entail_empty_rhs_heap: conseq must have empty heap

!!! WARNING logtime exception:0.
Procedure foo$int FAIL.(2)


Exception Failure("heap_entail_empty_rhs_heap: conseq must have empty heap") Occurred!


Error(s) detected when checking procedure foo$int

*************************************
******pure relation assumption*******
*************************************
[RELASS [P]: ( P(x)) -->  x<=0,
RELASS [P]: ( P(x)) -->  1<=x]
*************************************

*/
