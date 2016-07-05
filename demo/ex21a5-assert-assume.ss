

void foo(int x)
  requires true
  ensures true ;
{
    assert x'>=5 assume true;
    dprint;
}


void goo(int x)
  requires x>6
  ensures true ;
{
    assert x'>=5 assume true;
    dprint;
}


void foo2(int x)
  requires true
  ensures true ;
{
    assert x'>=5;
    dprint;
}

/*
# ex21a1 --efa-exc -dre "heap_entail"

Why @err_must still result in MaybeErr context
and not __ErrorMay exception?

(==solver.ml#14797==)
heap_entail_one_context_struc#2@5@4@3@2@1
heap_entail_one_context_struc#2 inp1 : EBase emp&5<=x'&{FLOW,(4,5)=__norm#E}[]
heap_entail_one_context_struc#2 inp2 : es_formula: htrue&x'=x & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 es_infer_obj: [@err_must]
 es_cond_path: [0]
 es_infer_vars_rel: []
 es_unsat_flag: false
heap_entail_one_context_struc#2 inp3 :is_folding:false
heap_entail_one_context_struc#2 inp4 :has_post:false
heap_entail_one_context_struc#2@5 EXIT: 
MaybeErr Context: 
                   fe_kind: MAY
                   fe_name: logical bug
                   fe_locs: {
                             fc_message:  true |-  5<=x'. LOCS:[2;6] (may-bug)
                             fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}}
[[empty]]
CEX:false



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
