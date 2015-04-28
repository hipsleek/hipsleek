data cell {
  int val;
}

void pre_call(cell x)
 case {
   x=null -> requires x::cell<_>
             ensures true;
  x!=null -> requires true
             ensures x::cell<_>;
}

bool foo2(cell x)
  requires true
  ensures res ;
{
  pre_call(x);
  dprint;
  return x!=null;
}

/*
# ex21a10.ss

This message seems wrong, --esl gave:
What happen to the MUST error.

 Try-Block:0::
 [
  Path: []
  State:es_formula: htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
        es_must_error: Some(do_unmatched_rhs : x'::cell<Anon_11>; true)
        es_final_error:[Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed ;
do_unmatched_rhs : x'::cell<Anon_11>]
  ]
 ]

# isn't it a MayErr?

id: 0; caller: []; line: 17; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@err_must]
 checkentail htrue&x'=x & x'=null & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  x'::cell<Anon_11>&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
   es_final_error:[do_unmatched_rhs : x'::cell<Anon_11>]
   ]


Proving precondition in method pre_call$cell Failed.
  (may) cause: OrL[do_unmatched_rhs : x'::cell<Anon_11>,valid]

# ex1a10 --efa-exc

However, we got:

Post condition cannot be derived:
  (may) cause:  true |-  res. LOCS:[19;15] (may-bug)


# --esl

pre-condition proving seems wrong
isn't there @err_may flag set/

 checkentail htrue&x'=x & x'!=null & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  htrue&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x & x'!=null&{FLOW,(4,5)=__norm#E}[]
   ]

Why post-cond has only message from one branch?
===============================================

Post condition cannot be derived:
  (may) cause:  true |-  res. LOCS:[19;15] (may-bug)

# For post-cond proving, I guess we should have flow inconsistency message
added?
 
id: 3; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@flow,@ver_post,@err_must]
 checkentail htrue&x'=x & x'=null & MayLoop[]&{FLOW,(6,10)=__Error#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
   es_final_error:[Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed ;
do_unmatched_rhs : x'::cell<Anon_11>]
   ]
 
id: 4; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [@err_must] globals: [@flow,@ver_post,@err_must]
 checkentail (exists Anon_1470: (htrue) * x'::cell<Anon_1470>&x'!=null & x'=x & 
res=v_boolean_19_1434' & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   (htrue) * x'::cell<Anon_1472>&x'!=null & x'=x & res=v_boolean_19_1434'&
     {FLOW,(4,11)=__MayError#E}[]
   es_final_error:[ true |-  res. LOCS:[19;15] (may-bug)]
   ]

*/
