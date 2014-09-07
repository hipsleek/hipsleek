UTPre@f fpre(int x).
UTPost@f fpost(int x).

int fact(int x)
  infer [@term]
  requires true & fpre(x)
  ensures res>=1 & fpost(x);
  /*  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
  */
{
  if (x==0) return 1;
  else return x*fact(x - 1);
}

/*
# fact.ss

non-linear cannot be handled. Can we at least remove or
transform them, so they can be partially handled.

Temporal Assumptions:
 termAssume 1<=v_int_16_922 & x'=v_int_16_919+1 & !(v_bool_15_880') & 
x'!=0 & !(v_bool_15_880') & x=x' & x'!=0 & v_int_16_879'=x'*v_int_16_922 & 
res=v_int_16_879' & fpost(v_int_16_877') --> fpost(x).

 termAssume x'=0 & x=x' & v_bool_15_880' & x'=x' & v_bool_15_880' & 
v_int_15_875'=1 & res=v_int_15_875' --> fpost(x).

 termAssume x'!=0 & x=x' & !(v_bool_15_880') & x'!=0 & !(v_bool_15_880') & 
x'=v_int_16_877'+1 & fpre(x) --> fpre(v_int_16_877').

Starting Omega...oc
Omega Error Exp:Globals.Illegal_Prover_Format("[omega.ml] Non-linear arithmetic is not supported by Omega.")

*/
