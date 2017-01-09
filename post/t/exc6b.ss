class Exp extends __Exc {
  int val;
}

int loop(int x)
  infer [@pre_n,@post_n]
  requires true
  ensures true 
    & flow __flow
    ;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  dprint;
  if (x>0) {
    if (x>100) raise new Exp(2222);
    x=x-1;
    loop(x);
  } 
  dprint;
  return x;
}

/*
# exc6b.ss

  infer [@pre_n,@post_n]
  requires true
  ensures true 
    & flow __flow
    ;

post-condition proving is lost in --esl log file
but present in exc6c.ss when we used norm in post-flow.

  infer [@pre_n,@post_n]
  requires true
  ensures true 
    ;


id: 6; caller: []; line: 18; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ post_1217,pre_1216]; c_heap: emp
 checkentail emp&0<x_1240 & pre_1216(x) & x_1240=x & v_bool_15_1198' & 0<x_1240 & 
v_bool_15_1198' & x_1240<=100 & !(v_bool_16_1195') & x_1240<=100 & 
!(v_bool_16_1195') & x'+1=x_1240&{FLOW,(4,5)=__norm#E}[]
 |-  emp&pre_1216(x')&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN pre_1216: ( x=1+x' & 0<=x' & x'<=99 & pre_1216(x)) -->  pre_1216(x')]
res:  1[
   emp&0<x_1240 & pre_1216(x) & x_1240=x & v_bool_15_1198' & 0<x_1240 & v_bool_15_1198' & x_1240<=100 & !(v_bool_16_1195') & x_1240<=100 & !(v_bool_16_1195') & x'+1=x_1240&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [post_1217; pre_1216]
   es_infer_rel: [RELDEFN pre_1216: ( x=1+x' & 0<=x' & x'<=99 & pre_1216(x)) -->  pre_1216(x')]
   ]
 
id: 7; caller: []; line: 18; classic: false; kind: PRE_REC; hec_num: 1; evars: []; infer_vars: [ post_1217,pre_1216]; c_heap: emp
 checkentail emp&0<x_1240 & pre_1216(x) & x_1240=x & v_bool_15_1198' & 0<x_1240 & 
v_bool_15_1198' & x_1240<=100 & !(v_bool_16_1195') & x_1240<=100 & 
!(v_bool_16_1195') & x'+1=x_1240&{FLOW,(4,5)=__norm#E}[]
 |-  emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]. 
res:  1[
   emp&0<x_1240 & pre_1216(x) & x_1240=x & v_bool_15_1198' & 0<x_1240 & v_bool_15_1198' & x_1240<=100 & !(v_bool_16_1195') & x_1240<=100 & !(v_bool_16_1195') & x'+1=x_1240&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [post_1217; pre_1216]
   es_infer_rel: [RELDEFN pre_1216: ( x=1+x' & 0<=x' & x'<=99 & pre_1216(x)) -->  pre_1216(x')]
   ]




*/
