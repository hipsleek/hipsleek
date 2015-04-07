pred_prim nondet<>
  inv true;

int nondeterm()
  requires true
  ensures res::nondet<>;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires Loop ensures false;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    foo(i);
  }
}

/*
# nondet/ex1.ss

# why is there an Loop{8:0} ??

Instead of false in post, can we have Loop as
its post-condition test?

  MayLoop |- Loop

  Loop    |- Loop

id: 6; caller: []; line: 16; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail i'::nondet{}<>&0<=i' & i_1436=i & 0<=i & 0<=i_1436 & v_bool_14_1402' & 
Loop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&Loop{ 8:0}[]&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   i'::nondet{}<>&0<=i' & i_1436=i & 0<=i & 0<=i_1436 & v_bool_14_1402'&{FLOW,(4,5)=__norm#E}[]
   ]

# why is Loop not present in LHS?
 
id: 7; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail i'::nondet{}<> * (htrue)&i'<0 & v_bool_14_1402' & 0<=i_1436 & 0<=i & 
i_1436=i&{FLOW,(4,5)=__norm#E}[]
 |-  hfalse&false&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  failctx
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message:  true |-  false. LOCS:[0] (RHS: contradiction)
                   fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}}
[[empty]]false
*/
