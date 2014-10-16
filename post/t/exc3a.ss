class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    raise new Exp(2222);
    loop(x);
  } 
  //else {return x+1;}
  //dprint;
  return x+1111;
}

/*
# exc3.ss

 infer [@post_n]
  requires true
  ensures true;

Post condition cannot be derived:
Empty list_partial_contex


Why is failure not reported by --esl?
when we have empty lpc?

id: 4; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ post_1215]; c_heap: emp
 checkentail emp&x'<=0 & x'=x & !(v_bool_12_1195') & x'<=0 & !(v_bool_12_1195') & 
v_int_18_1198'=1111+x' & res=v_int_18_1198'&{FLOW,(4,5)=__norm}[]
 |-  emp&post_1215(x,res)&{FLOW,(4,5)=__norm}[]. 
pure rel_ass: [RELDEFN post_1215: ( x=res-1111 & res<=1111) -->  post_1215(x,res)]
res:  1[
   emp&x'<=0 & x'=x & !(v_bool_12_1195') & x'<=0 & !(v_bool_12_1195') & v_int_18_1198'=1111+x' & res=v_int_18_1198'&{FLOW,(4,5)=__norm}[]
   es_infer_vars/rel/templ: [post_1215]
   es_infer_rel: [RELDEFN post_1215: ( x=res-1111 & res<=1111) -->  post_1215(x,res)]
   ]




*/
