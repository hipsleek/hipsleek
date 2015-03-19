UTPre@f fpre(int x).
UTPost@f fpost(int x).

void f(int x)
  infer [@term]
  //requires fpre(x)
  //ensures fpost(x);
  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
  
{
  if (x < 0) return;
  else f(x - 1);
}

/*
# termu-1c.ss

Why isn't @term entailment logged?

id: 1; caller: []; line: 10; classic: false; kind: POST; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&v' & x'<0 & x=x' & x<0&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'<0 & x<0 & x=x' & v_bool_15_876' & x'<0 & v_bool_15_876'&{FLOW,(24,25)=__norm}[]
   ]
 
id: 3; caller: []; line: 16; classic: false; kind: PRE; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&v'=1 & !(v1') & 0<=x' & x=x' & 0<=x&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&0<=x' & 0<=x & x=x' & !(v_bool_15_876') & 0<=x' & !(v_bool_15_876') & v_int_16_874'=1&{FLOW,(24,25)=__norm}[]
   ]

# termu-1c.ss


// why did we generate this as base-case?

 termAssume 0<=x' & 0<=x & x=x' & !(v_bool_15_876') & 0<=x' & 
!(v_bool_15_876') & x'=v_int_16_922+1 & v_int_16_922<0 --> fpost(x).

 termAssume 0<=v_int_16_924 & x'=v_int_16_924+1 & !(v_bool_15_876') & 
0<=x' & !(v_bool_15_876') & x=x' & 0<=x & 
0<=x' & fpost(v_int_16_875') --> fpost(x).

 termAssume 0<=x' & 0<=x & x=x' & !(v_bool_15_876') & 0<=x' & 
!(v_bool_15_876') & x'=v_int_16_875'+1 & 
0<=v_int_16_875' & fpre(x) --> fpre(v_int_16_875').


Base/Rec Case Splitting:
[	f: [[2] 1<=x@R,[3] x=0@B]
]
Starting z3... 
Termination Inference Result:
f:  case {
  1<=x -> requires emp & Term[0+(1*x)]
 ensures emp & true; 
  x=0 -> requires emp & Term[]
 ensures emp & true; 
  }

*/
