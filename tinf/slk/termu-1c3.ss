UTPre@f fpre(int x).
UTPost@f fpost(int x).

void f(int x)
  infer [@term]
  requires fpre(x)
  ensures fpost(x);
  /*
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
  */
{
  if (x < 0) return;
  else f(x - 1);
}

/*
# term-1c3.ss

!!!Number of sleek log entries 7
!!!Logging logs/sleek_log_termu-1c3_ss.txt

Why only 1 logged entry printed?

id: 2; caller: []; line: 16; classic: false; kind: PRE; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&v'=1 & !(v1') & 0<=x' & x=x'&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&0<=x' & x=x' & !(v_bool_15_874') & 0<=x' & !(v_bool_15_874') & v_int_16_872'=1&{FLOW,(24,25)=__norm}[]
   ]


Temporal Assumptions:
 termAssume x'=v_int_16_907+1 & !(v_bool_15_874') & 0<=x' & 
!(v_bool_15_874') & x=x' & 0<=x' & fpost(v_int_16_873') --> fpost(x).

 termAssume x'<0 & x=x' & v_bool_15_874' & x'<0 & 
v_bool_15_874' --> fpost(x).

 termAssume 0<=x' & x=x' & !(v_bool_15_874') & 0<=x' & !(v_bool_15_874') & 
x'=v_int_16_873'+1 & fpre(x) --> fpre(v_int_16_873').

*/
