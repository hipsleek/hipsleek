data cell {
  int val;
}

void pre_call(cell x)
 case {
   x!=null -> requires x::cell<_>
             ensures true;
  x=null -> requires true
    ensures x=null; //x::cell<_>;
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
# ex21a10.ss --efa-exc

# Seems to be a wrong post-cond error

Post condition cannot be derived:
  (may) cause:  true |-  res. LOCS:[19;15] (may-bug)

dprint(simpl): ex21a10-case-spec.ss:18: ctx:  List of Failesc Context: [FEC(0, 1, 1  [])]
Escaped States:
[
 
 Try-Block:0::
 [
  Path: []
  State:htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
        es_final_error:[Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed (may);
do_unmatched_rhs : x'::cell<Anon_11>(must)]
  ]
 ]
Successful States:
[
 Label: []
 State:(exists Anon_1470: (htrue) * x'::cell<Anon_1470>&x'!=null & x'=x&
         {FLOW,(4,5)=__norm#E}[]
       es_cond_path: [0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: []
 Exc:Some
 ]

--esl

# OK but not captured by post-cond failure message

id: 3; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post,@err_must]
 checkentail htrue&x'=x & x'=null & MayLoop[]&{FLOW,(6,10)=__Error#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
   es_final_error:[1.2c: ante flow:__Error#E conseq flow: __norm#E are incompatible flow types;
Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed (may);
do_unmatched_rhs : x'::cell<Anon_11>(must); 
                   Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed (may);
do_unmatched_rhs : x'::cell<Anon_11>(must)]
   ]

# why is res=x'!=null not captured?
 
id: 4; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post,@err_must]
 checkentail (exists Anon_1470: (htrue) * x'::cell<Anon_1470>&x'!=null & x'=x & 
res=v_boolean_19_1434' & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   (htrue) * x'::cell<Anon_1472>&x'!=null & x'=x & res=v_boolean_19_1434'&
     {FLOW,(4,11)=__MayError#E}[]
   es_final_error:[ true |-  res. LOCS:[19;15] (may-bug)]
   ]

=======================================================================================================


  (may) cause: OrL
 [AndR[
1.2b: ante flow:__MayError#E conseq flow: __norm#E are incompatible flow types(may);
Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed (may);
do_unmatched_rhs : x'::cell<Anon_11> (must), 

true |-  res. LOCS:[0;15] (may-bug)], 

true |-  res. LOCS:[19;15] (may-bug)]


Context of Verification Failure: _0:0_0:0
Last Proving Location: ex21a10-case-spec.ss_19:2_19:16
ERROR: at _0:0_0:0
Message: Post condition cannot be derived.
Procedure foo2$cell FAIL.(2)
Exception Failure("Post condition cannot be derived.") Occurred!
Error(s) detected when checking procedure foo2$cell

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
# improve printing
# has one branch of post-cond error been dropped?


id: 3; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post,@err_must]
 checkentail htrue&x'=x & x'=null & MayLoop[]&{FLOW,(4,11)=__MayError#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   or[htrue&x'=x & x'=null&{FLOW,(6,10)=__Error#E}[]
      es_final_error:[Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed ;
do_unmatched_rhs : x'::cell<Anon_11>]; htrue&
                                                                    x'=x & 
                                                                    x'=null&
                                                                   {FLOW,(4,11)=__MayError#E}[]
                                                                    es_final_error:[ true |-  res. LOCS:[0;15] (may-bug); 
                                                                    Proving precondition in method pre_call$cell(1 File "ex21a10-case-spec.ss",Line:17,Col:2) Failed ;
do_unmatched_rhs : x'::cell<Anon_11>]]
   ]
 
id: 5; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post,@err_must]
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
