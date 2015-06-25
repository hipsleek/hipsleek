
void foo(int x)
  requires true
  ensures true & flow __Exc ;
{
    assert x'>=5 assume true;
    dprint;
}

/*
# ex21a51 --efa-exc -dre "heap_entail"

# why is it a wrong post-condition failure?
     (may) cause:  true |-  5<=x'. LOCS:[2;6] (may-bug)

# It should be:
      x=x' & flow __MayError |- true & flow __norm.

Or at least:
      x=x' & flow __MayError |- false.

I think the current failure here is from assert failure.



!!! **typechecker.ml#2071:Dprint:[x]
dprint(simpl): ex21a51-assert-assume.ss:7: ctx:  List of Failesc Context: [FEC(0
, 0, 1  [])]

Successful States:
[
 Label: []
 State:htrue&x'=x&{FLOW,(4,5)=__norm#E}[]

 ]

Post condition cannot be derived:
  (may) cause:  true |-  5<=x'. LOCS:[2;6] (may-bug)

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex21a51-assert-assume.ss_6:4_6:28

--esl

// correct

id: 0; caller: []; line: 6; classic: false; kind: Assert/Assume; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@err_must]
 checkentail htrue&x'=x&{FLOW,(4,5)=__norm#E}[]
 |-  emp&5<=x'&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x&{FLOW,(4,11)=__MayError#E}[]
   ]

// incorrect antecedent

id: 1; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@flow,@ver_post,@err_must]
 checkentail htrue&x'=x&{FLOW,(4,5)=__norm#E}[]
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x&{FLOW,(4,5)=__norm#E}[]
   ]
*/
