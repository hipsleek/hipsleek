class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true  & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    //dprint;
    raise new Exp(2222);
    loop(x);
  } 
  //else {return x+1;}
  // dprint;
  return x+1111;
}

/*
# exc3.ss

 infer [@post_n]
  requires true
  ensures true;

infer fails to capture recursive scenario

Escaped States:
[
 
 Try-Block:0::
 [
  Path: [(,0 ); (,1 )]
  State:(exists v_int_13_1192': v_Exp_13_1193'::Exp<v_int_13_1192'>&0<x' & x'=x & v_bool_12_1195' & 0<x' & v_bool_12_1195' & v_int_13_1192'=2 & eres=v_Exp_13_1193'&{FLOW,(25,26)=Exp})[]
        es_ho_vars_map: []EXISTS(v_int_13_1192': v_Exp_13_1193'::Exp<v_int_13_1192'>&0<x' & x'=x & v_bool_12_1195' & 0<x' & v_bool_12_1195' & v_int_13_1192'=2 & eres=v_Exp_13_1193')[]

  ]
 ]
Successful States:
[
 Label: [(,1 ); (,2 )]
 State:emp&x'<=0 & x'=x & !(v_bool_12_1195') & x'<=0 & !(v_bool_12_1195')&{FLOW,(4,5)=__norm}[]
       es_ho_vars_map: []emp&x'<=0 & x'=x & !(v_bool_12_1195') & x'<=0 & !(v_bool_12_1195')

 ]


*************************************
*******pure relation assumption ******
*************************************
[RELDEFN post_1214: ( x=res-1 & res<=1) -->  post_1214(x,res)]
*************************************


*/
