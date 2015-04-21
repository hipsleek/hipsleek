/* pred_prim nondet<> */
/*   inv true; */

int nondeterm()
  requires true
  ensures true;

void foo(int i) 
  case {
    i < 0 -> requires Term[] ensures true;
    i >=0 -> requires Loop ensures true;
  }
{ 
  if (i>=0) {
    i = nondeterm();
    //assume i'>=0;
    infer_assume [i];
    foo(i);
  }
}

/*

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
