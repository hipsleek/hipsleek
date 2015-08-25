/* pred_prim nondet<> */
/*   inv true; */

int nondeterm()
  requires true
  ensures true;

void foo(int xxx) 
  case {
    xxx < 0 -> requires Term[] ensures true;
    xxx >=0 -> requires Loop ensures true;
  }
{ 
  if (xxx>=0) {
    int xxx2 = nondeterm();
    //assume xxx'>=0;
    //infer_assume [xxx2];
    foo(xxx - 1);
  }
}

/*

# nondet/ex1d-loop.ss

  (* TODO : need to handle pure_branches in future ? *)
  (* unfixed 13008 that was for rb.ss -p del *)
  (* relation to infer need to be made explicit *)
  if no_infer_rel estate (* && no_infer_hp_rel estate *) then (estate,lhs_mix,rhs_mix,None,[])
  else

(==solver.ml#3716==)
infer_collect_rel@12@8
infer_collect_rel inp1 : es_formula: hfalse&false&{FLOW,(4,5)=__norm#E}[]
 es_cond_path: [1]
 es_var_measures 1: Some(Term[34]{34})
 es_infer_vars_rel: [3]
infer_collect_rel inp2 :[3]
infer_collect_rel inp3 : false
infer_collect_rel inp4 : false
infer_collect_rel inp5 : MayLoop[]
infer_collect_rel@12 EXIT:( false,2: true,3:[RELDEFN 3: ( false) -->  MayLoop[]],4:None,5:[])

Why cppo not working here...with "",0??

(==#0==)
is_inferred_pre_ctx@13@8
is_inferred_pre_ctx inp1 : es_formula: hfalse&false&{FLOW,(4,5)=__norm#E}[]
 es_cond_path: [1]
 es_var_measures 1: Some(Term[34]{34})
 es_infer_vars_rel: [3]
 es_infer_rel: [RELDEFN 3: ( false) -->  MayLoop[]]
is_inferred_pre_ctx@13 EXIT:true

# nondet/ex1d-loop.ss

infer_assume[i'] will attempt to infer a
pre-condition that can be assumed on i'
to allow the verification to succeed.

// it seems we did not entail false below?

Termination checking result: 
(0) (ERR: unexpected unsound Loop at return)

Why did we have RELDEFN below? Who needed them?
 pure rel_ass: [
   RELDEFN 3: ( false) -->  MayLoop[], 
   RELDEFN 3: ( false) -->  MayLoop[]]

   In the presence of Loop, why did we not have:
   infer [i'] current-state |- false?

Other sleek proving steps:

id: 1; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail emp&!(v_bool_14_1401') & i'<0 & i<0 & i'=i & Term[34]&
{FLOW,(4,5)=__norm#E}[]
 |-  htrue&i<0&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN 3: ( false) -->  MayLoop[],
RELDEFN 3: ( false) -->  MayLoop[]]
ho_vars: nothing?
res:  1[
   emp&!(v_bool_14_1401') & i'<0 & i<0 & i'=i&{FLOW,(4,5)=__norm#E}[]
   ]

id: 7; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ i']; c_heap: emp
 checkentail htrue&i'<0 & v_bool_14_1401' & 0<=i_1435 & 0<=i & i_1435=i & Loop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  htrue&0<=i&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&i'<0 & v_bool_14_1401' & 0<=i_1435 & 0<=i & i_1435=i&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [i']
   ]
 
id: 8; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ i']; c_heap: emp
 checkentail htrue&0<=i' & v_bool_14_1401' & 0<=i_1435 & 0<=i & i_1435=i & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  htrue&0<=i&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
   htrue&0<=i' & v_bool_14_1401' & 0<=i_1435 & 0<=i & i_1435=i&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [i']
   ]

====================================================

It should also print the inferred 
local (non-deterministic) condition.

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires Loop ensures true;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    //assume i'>=0;
    infer_assume[i'];
    foo(i);
  }
}

*/
