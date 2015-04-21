void foo(int x)
  requires true
  ensures true;
{
  //assert false assume true;
    assert false;
    assert x'<0;
}

/*

!!! **solver.ml#8027:xpure_lhs_h1_sym (wo pure): true
assert:ex22-assert-assume.ss:6: 4:  : ok


!!! **solver.ml#8025:xpure_lhs_h1: true
!!! **solver.ml#8026:xpure_lhs_h0_sym (wo pure): true
!!! **solver.ml#8027:xpure_lhs_h1_sym (wo pure): true
assert:ex22-assert-assume.ss:7: 4:  : ok

*/
