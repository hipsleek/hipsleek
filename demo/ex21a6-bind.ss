data cell {
  int val;
}

int foo2(cell x)
  requires true
  ensures true ;
{
  int x = x.val;
  dprint;
  return x;

}

/*
# ex21a6
 --efa-exc -dre "heap_entail"

# Why is there empty_context?


Checking procedure foo2$cell... 
( []) :ex21a6-bind.ss:9: 10: bind: node  x'::cell<val_9_1431'>@L cannot be deriv
ed from context

(Cause of Bind Failure):ex21a6-bind.ss:9: 10:  List of Failesc Context: [FEC(

!! **typechecker.ml#2065:Dprint:[x_15,x]
dprint:ex21a6-bind.ss:10 empty context

Can we have failed (MAY ERROR)
     or failed (MUST ERROR) 
for assert wo assume.



# ex21a6
 --efa-exc -dre "heap_entail"

Why below did not trigger an error exception?

(==solver.ml#14798==)
heap_entail_one_context_struc#2@5@4@3@2@1
heap_entail_one_context_struc#2 inp1 : EBase x'::cell<val_9_1431'>@L&{FLOW,(1,28)=__flow#E}[]
heap_entail_one_context_struc#2 inp2 : es_formula: htrue&x'=x & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 es_infer_obj: [@err_must]
 es_cond_path: [0]
 es_infer_vars_rel: []
heap_entail_one_context_struc#2 inp3 :is_folding:false
heap_entail_one_context_struc#2 inp4 :has_post:true
heap_entail_one_context_struc#2@5 EXIT: 
MaybeErr Context: 
                   fe_kind: MAY
                   fe_name: separation entailment
                   fe_locs: {
                             fc_message: do_unmatched_rhs : x'::cell<val_9_1431'>@L
                             fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}}
[[ COND ==>  UnmatchedRHSData ==> ]]
CEX:false

Checking procedure foo2$int... 
assert/assume:ex21a5-assert-assume.ss:23: 4:  : failed


*/
