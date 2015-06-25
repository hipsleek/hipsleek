data cell {
  int val;
}

void pre_call(cell x)
  infer [@pre_must
  ]
  requires x::cell<_> 
  ensures x::cell<3>;
/* 
  # ex21a12.ss

void pre_call(cell x)
  infer [@pre_must]
  requires x::cell<_> 
  ensures x::cell<3>;

   this @pre_must tag indicates a pre-condition that must be
   be satisfied. When tag is present, we must ensure
   must failure if there is contradiction with the
   pre-condition. This is we must use wrap_must_err for
   such pre-condition. This may be for primitives with
   must rather than may pre-conditions

../hip ex21a12-pre-must.ss --efa-exc -p foo2

# without assume false
Post condition cannot be derived:
OrL[
  (must) cause: 1.2c: ante flow:__Error#E conseq flow: __norm#E are incompatible flow types;
Proving precondition in method pre_call$cell(1 File "ex21a12-pre-must.ss",Line:32,Col:15) Failed (must);
do_unmatched_rhs : x'::cell<Anon_11>(must),
  (must) cause:  !(res) |-  res. LOCS:[35;30] (must-bug)
]

# with assume false
Post condition cannot be derived:
  (must) cause: 1.2c: ante flow:__Error#E conseq flow: __norm#E are incompatible flow types;
Proving precondition in method pre_call$cell(1 File "ex21a12-pre-must.ss",Line:42,Col:15) Failed (must);
do_unmatched_rhs : x'::cell<Anon_11>(must)

*/


bool foo2(cell x)
  requires true
  ensures res ;
{
  if (x==null) pre_call(x);
  //assume false;
  dprint;
  return x==null;
}


bool foo3(cell x)
  requires true
  ensures res ;
{
  if (true) pre_call(x);

  dprint;
  return x==null;
}



/*

# ex21a11


!!! **wrapper.ml#148:Calling wrap_err_pre
Post condition cannot be derived:
  (may) cause: AndR[1.2b: ante flow:__MayError#E conseq flow: __norm#E are incompatible flow types;
Proving precondition in method pre_call$cell(1 File "ex21a11-or.ss",Line:12,Col:15) Failed ;
do_unmatched_rhs : x'::cell<Anon_11>, true |-  res. LOCS:[0;10] (may-bug)]
OrL
  (must) cause:  !(res) |-  res. LOCS:[15;10] (must-bug)
Context of Verification Failure: _0:0_0:0
Last Proving Location: ex21a11-or.ss_15:2_15:16
ERROR: at _0:0_0:0
Message: Post condition cannot be derived.

How come another error below is not captured?
Is it there? The printout does not seem complete.

id: 9; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post,@err_must]
 checkentail htrue&res=v_boolean_15_1439' & x'!=null & !(v_boolean_15_1439') & x'=x & 
!(v_bool_12_1437') & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&res&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&res=v_boolean_15_1439' & x'!=null & !(v_boolean_15_1439') & x'=x & 
     !(v_bool_12_1437')&{FLOW,(6,10)=__Error#E}[]
   es_final_error:[ !(res) |-  res. LOCS:[15;10] (must-bug)]
   ]

*/
