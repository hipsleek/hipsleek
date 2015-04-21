void failmeth()
 requires false
 ensures true;

void foo(int x)
  requires true
  ensures true;
{
  if (x>0) {
    assert false assume true;
    dprint;
    //assert false;
    assert x'<0;
  }
}

/*
# ex21i  --dis-efa-exc

This should have same outcome as ex21

Last Proving Location: ex21-assert-assume.ss_10:4_10:14
Procedure foo$int FAIL.(2)
Exception Failure("Proving precond failed") Occurred!


GOT below instead:

Checking procedure foo$int... 
assert/assume:ex21i-assert-assume.ss:10: 4:  : failed
!!! **typechecker.ml#2012:Dprint:[x]
dprint:ex21i-assert-assume.ss:11 empty context
Context of Verification Failure: _0:0_0:0
Last Proving Location: ex21i-assert-assume.ss_13:4_13:15
ERROR: at ex21i-assert-assume.ss_13:4_13:15
Message: heap_entail_failesc_prefix_init : encountered an empty list_partial_context 


*/
