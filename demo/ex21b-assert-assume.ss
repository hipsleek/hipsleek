void failmeth ()
 requires false
 ensures true;

void foo(int x)
  requires true
  ensures true;
{
  if (x>0) {
    failmeth();
    //assert false assume true;
    dprint;
    //assert false;
    assert x'<0;
  }
}

/*
# ex21b

Checking procedure foo$int... 
!!! **typechecker.ml#2010:Dprint:[x]
dprint:ex21b-assert-assume.ss:12 empty context
Context of Verification Failure: _0:0_0:0

Last Proving Location: ex21b-assert-assume.ss_14:4_14:15

ERROR: at ex21b-assert-assume.ss_14:4_14:15
Message: heap_entail_failesc_prefix_init : encountered an empty list_partial_context 


Procedure foo$int FAIL.(2)


Exception Failure("heap_entail_failesc_prefix_init : encountered an empty list_partial_context \n") Occurred!


Error(s) detected when checking procedure foo$int
Stop Omega... 60 invocations 
0 false contexts at: ()


*/
