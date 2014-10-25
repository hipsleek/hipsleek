class Exp extends __Exc {
  int val;
}

void loop(ref int x)
  infer [@post_n]
  requires true
  ensures  true & flow __flow;
{
  if (x>0) {
    /* raise new Exp(2); */
    x = x-1;
    loop(x);
  } else {
    return;
  }
}

/*
# flow2.ss

Got:
*************************************
***pure relation assumption (norm)***
*************************************
[RELDEFN post_1210: ( 0<=x_1227 & x=1+x_1227 & post_1210(x_1227,x')) -->  post_1210(x,x'),
RELDEFN post_1210: ( x=x' & x'<=0) -->  post_1210(x,x')]
*************************************

Expecting: post_1210(__norm#): ( x=x' & x'<=0) -->  post_1210(x,x')]
why wasn't this captured in the --esl log?

id: 7; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ post_1210]; c_heap: emp
 checkentail emp&x'<=0 & x'=x & !(v_bool_10_1193') & x'<=0 & !(v_bool_10_1193')&
{FLOW,(4,5)=__norm#E}[]
 |-  emp&post_1210(x,x')&{FLOW,(1,30)=__flow#E}[]. 
pure rel_ass: [RELDEFN post_1210: ( x=x' & x'<=0) -->  post_1210(x,x')]
res:  1[
   emp&x'<=0 & x'=x & !(v_bool_10_1193') & x'<=0 & !(v_bool_10_1193')&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [post_1210]
   es_infer_rel: [RELDEFN post_1210: ( x=x' & x'<=0) -->  post_1210(x,x')]
   ]

*/
