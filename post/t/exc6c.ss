class Exp extends __Exc {
  int val;
}

int loop(int x)
  infer [@pre_n,@post_n]
  requires true
  ensures true 
  //& flow __flow
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
# exc6c.ss

  infer [@pre_n,@post_n]
  requires true
  ensures true 
  //& flow __flow
    ;

post-condition proving is present here when
norm is used.

id: 8; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ post_1217,pre_1216]; c_heap: emp
 checkentail (exists v_int_15_1197': emp&0<x_1240 & pre_1216(x) & x_1240=x & 
v_bool_15_1198' & 0<x_1240 & v_bool_15_1198' & x_1240<=100 & 
!(v_bool_16_1195') & x_1240<=100 & !(v_bool_16_1195') & x'+1=x_1240 & 
post_1217(x',v_int_15_1197') & res=x'&{FLOW,(4,5)=__norm#E})[]
 |-  emp&post_1217(x,res)&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN post_1217: ( x=1+res & 0<=res & res<=99 & pre_1216(x) & post_1217(res,v_int_15_1247)) -->  post_1217(x,res),
RELDEFN pre_1216: ( x=1+x' & 0<=x' & x'<=99 & pre_1216(x)) -->  pre_1216(x')]
res:  1[
   emp&0<x_1240 & pre_1216(x) & x_1240=x & v_bool_15_1198' & 0<x_1240 & v_bool_15_1198' & x_1240<=100 & !(v_bool_16_1195') & x_1240<=100 & !(v_bool_16_1195') & x'+1=x_1240 & post_1217(x',v_int_15_1247) & res=x'&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [post_1217; pre_1216]
   es_infer_rel: [RELDEFN pre_1216: ( x=1+x' & 0<=x' & x'<=99 & pre_1216(x)) -->  pre_1216(x'); 
                  RELDEFN post_1217: ( x=1+res & 0<=res & res<=99 & pre_1216(x) & post_1217(res,v_int_15_1247)) -->  post_1217(x,res)]
   ]
 
id: 9; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ post_1217,pre_1216]; c_heap: emp
 checkentail emp&x'<=0 & pre_1216(x) & x'=x & !(v_bool_15_1198') & x'<=0 & 
!(v_bool_15_1198') & res=x'&{FLOW,(4,5)=__norm#E}[]
 |-  emp&post_1217(x,res)&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN post_1217: ( x=res & res<=0 & pre_1216(x)) -->  post_1217(x,res)]
res:  1[
   emp&x'<=0 & pre_1216(x) & x'=x & !(v_bool_15_1198') & x'<=0 & !(v_bool_15_1198') & res=x'&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [post_1217; pre_1216]
   es_infer_rel: [RELDEFN post_1217: ( x=res & res<=0 & pre_1216(x)) -->  post_1217(x,res)]
   ]




*/
