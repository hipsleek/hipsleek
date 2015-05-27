
void foo(int x)
  requires x=0
  ensures true ;
{
    assert x'>=5 assume true;
    dprint;
}

/*
# ex21a52 --efa-exc

Why am I not getting the original must failure?
  Path: []
  State:emp&x=0 & x'=x&{FLOW,(6,10)=__Error#E}[]
  Exc:Some

Post condition cannot be derived:
  (must) cause: 1.2: ante flow:__Error#E conseq flow: __norm#E are incompatible flow types

--dfa-exc

assert/assume:ex21a52-assert-assume.ss:6: 4:  : failed (must)
  (must) cause:  x'=0 |-  5<=x'. LOCS:[3;2;6] (must-bug)
Context of Verification Failure: _0:0_0:0
Last Proving Location: ex21a52-assert-assume.ss_6:4_6:28
Procedure foo$int FAIL.(2)
Exception Failure("Proving assert/assume failed") Occurred!

# ex21a51 --efa-exc

  State:htrue&x'=x&{FLOW,(4,11)=__MayError#E}[]
  Exc:Some
  ]
 ]

Post condition cannot be derived:
  (may) cause: (Proving assert/assume in method foo$int (1 File "ex21a51-assert-assume.ss",Line:6,Col:4) Failed.)  true |-  5<=x'. LOCS:[2;6] (may-bug)

*/
