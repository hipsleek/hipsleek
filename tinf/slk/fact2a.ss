UTPre@fact fpre(int x).
UTPost@fact fpost().

int fact(int x)
  infer [@term]
  case {
    x = 0 -> requires Loop ensures true;
    x != 0 -> requires fpre(x) ensures res>=1 & fpost();
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
# fact2a.ss

Why continue with term inference after post-cond 
proving has failed?

Post condition cannot be derived:
  (may) cause:  res=v_int_13_948+1 |-  1<=res. LOCS:[13;8] (may-bug)

Context of Verification Failure: 1 File "fact2a.ss",Line:8,Col:39
Last Proving Location: 1 File "fact2a.ss",Line:13,Col:14

Temporal Assumptions:
 termAssume 1<=v_int_13_951 & 0<=v_int_13_948 & x'=v_int_13_948+1 & 
!(v_bool_12_882') & x'!=0 & !(v_bool_12_882') & x=x' & 0<=x & x'!=0 & 
v_int_13_881'=v_int_13_951+1 & res=v_int_13_881' & fpost() --> fpost().

 termAssume x'=0 & 0<=x & x=x' & v_bool_12_882' & x'=x' & v_bool_12_882' & 
v_int_12_876'=1 & res=v_int_12_876' --> fpost().

 termAssume x'!=0 & 0<=x & x=x' & !(v_bool_12_882') & x'!=0 & 
!(v_bool_12_882') & v_int_13_880'=1 & x'=v_int_13_878'+1 & 
0<=v_int_13_878' & fpre(x) --> fpre(v_int_13_878').


Base/Rec Case Splitting:
[	f: [[2] true@ML]
]
Termination Inference Result:
f:  case {
  true -> requires emp & MayLoop[]
 ensures emp & true; 
  }

Termination checking result: 
(7)->(13) (MayTerm ERR: not decreasing)  Term[29] ->  Term[29]

*/
