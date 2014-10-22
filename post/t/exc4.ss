class Exp extends __Exc {
  int val;
}

int loop(int x)
//infer [@post_n]
  requires true
  ensures  res=x+1111 & flow __norm;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    raise new Exp(888);
    loop(x);
    /* return 2; */
  } else {
    return x+1111;
  }
  dprint;
}

/*
# exc4.ss


Provable but unsound in check_post.

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:es_formula: 
        emp&x'<=0 & x'=x & !(v_bool_12_1206') & x'<=0 & !(v_bool_12_1206') & 
        v_int_17_1204'=1+x' & res=v_int_17_1204'&{FLOW,(4,5)=__norm}[]
       es_history: [emp; emp; emp; emp]
       es_cond_path: [2; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: []
       es_unsat_flag: false;
 Label: [(,0 ); (,1 )]
 State:es_formula: 
        (exists v_int_13_1201': v_Exp_13_1202'::Exp<v_int_13_1201'>&0<x' & 
        x'=x & v_bool_12_1206' & 0<x' & v_bool_12_1206' & v_int_13_1201'=2 & 
        eres=v_Exp_13_1202'&{FLOW,(25,26)=Exp})[]
       es_history: [emp; emp]
       es_cond_path: [1; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: []
 ]
check_post inp2 :( emp&res=1+x&{FLOW,(4,5)=__norm}[], EBase emp&res=1+x&{FLOW,(4,5)=__norm}[])
check_post@1 EXIT: List of Partial Context: []

*/
