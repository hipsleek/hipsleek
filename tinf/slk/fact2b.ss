UTPre@f fpre(int x).
UTPost@f fpost().

int fact(int x)
//infer [@term]
  case {
    x = 0 -> requires true ensures res>=1;
    x != 0 -> requires true ensures res>=1 ;
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
# fact2a.ss

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
