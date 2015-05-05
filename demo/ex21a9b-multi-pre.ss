data cell {
  int val;
}

void pre_call(cell x)
  requires x::cell<_>
  ensures true;
//requires true ensures x::cell<_>;

int foo2(cell x)
  requires true
  ensures res=4 ;
{
  pre_call(x);
  dprint;
  return 3;

}

/*
# ex21a9b.ss --efa-exc 

Message below is incorrect since error flow and
__norm flow are incompatible!.

Post condition cannot be derived:
  (must) cause:  res=3 |-  res=4. LOCS:[16;12] (must-bug)

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex21a9-multi-pre.ss_16:9_16:10

=================================
# ex21a9.ss --efa-exc

// where is incompatible flow message?

Post condition cannot be derived:
  (may) cause: (Proving precondition in method pre_call$cell(1 File "ex21a9-multi-pre.ss",Line:14,Col:2) Failed ) do_unmatched_rhs : x'::cell<Anon_11>


================================================

--efa-exc triggers must-err exception for pre-condition checking
# Why is there a verification failure 
and empty context?

Checking procedure foo2$cell... 
!!! **typechecker.ml#2065:Dprint:[x]
dprint:ex21a8-pre.ss:14 empty context
Procedure foo2$cell result FAIL.(1)

However, heap_entail seems fine:

(==solver.ml#4304==)
heap_entail_one_context#13@8@7@6@5@4@3@2@1
heap_entail_one_context#13 inp1 : es_formula: htrue&x'=x & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 es_infer_obj: [@err_must]
 es_gen_impl_vars: [Anon_11]
 es_cond_path: [0]
 es_infer_vars_rel: []
heap_entail_one_context#13 inp2 : x'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]
heap_entail_one_context#13@8 EXIT: [
  htrue&x'=x&{FLOW,(4,11)=__MayError#E}[]
  ]

--dis-efa-exc triggers pre-cond failure

Starting Omega.../usr/local/bin/oc

Checking procedure foo2$cell... 
Proving precondition in method pre_call$cell Failed.
  (may) cause: do_unmatched_rhs : x'::cell<Anon_11>

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex21a8-pre.ss_13:2_13:13

Procedure foo2$cell FAIL.(2)

--efa-may

sleek triggers @err_may. 

id: 0; caller: []; line: 13; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_may] globals: [@err_may]
 checkentail htrue&x'=x&{FLOW,(4,5)=__norm#E}[]
 |-  x'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x&{FLOW,(4,11)=__MayError#E}[]
   ]

# However, we still get empty context error.

!!! **typechecker.ml#2065:Dprint:[x]
dprint:ex21a8-pre.ss:14 empty context
Procedure foo2$cell result FAIL.(1)


*/
