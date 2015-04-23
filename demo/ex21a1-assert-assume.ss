
void foo(int x)
  requires true
  ensures true ;
{
    assert x'>=5 assume true;
    dprint;
}

/*
# ex21a1 --efa-exc

Context of Verification Failure: _0:0_0:0
Last Proving Location: ex21a1-assert-assume.ss_6:4_6:28
Procedure foo$int FAIL.(2)
Exception Failure("Proving assert/assume failed") Occurred!

Why isn't dprint working?
I expect MayError exception to be printed.
How come --efa not working?

id: 0; caller: []; line: 6; classic: false; kind: Assert/Assume; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail htrue&x'=x&{FLOW,(4,5)=__norm#E}[]
 |-  emp&5<=x'&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  failctx
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message:  true |-  5<=x'. LOCS:[2;6] (may-bug)
                   fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}}
[[empty]]false

*/
