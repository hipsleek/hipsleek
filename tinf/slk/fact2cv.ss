UTPre@fact fpre(int x).
UTPost@fact fpost(int x).

int fact(int x)
//infer [@term]
  case {
    x = 0 -> ensures res>=1 ;
    x != 0 -> ensures res>=1 ;
  }

{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}
/*
# fact2c.ss

id: 3; caller: []; line: 13; classic: false; kind: PRE; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&v'=1 & v1'=1 & !(v2') & x'!=0 & x=x' & x!=0&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'!=0 & x!=0 & x=x' & !(v_bool_12_886') & x'!=0 & !(v_bool_12_886') & v_int_13_884'=1 & v_int_13_881'=1&{FLOW,(24,25)=__norm}[]
   ]
 
id: 7; caller: []; line: 13; classic: false; kind: PRE; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&1<=v' & x'=0+1 & v1'=1 & !(v2') & x'!=0 & x=x' & x!=0&
{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'!=0 & x!=0 & x=x' & !(v_bool_12_886') & x'!=0 & !(v_bool_12_886') & v_int_13_884'=1 & x'=0+1 & 1<=v_int_13_883' & 0=0&{FLOW,(24,25)=__norm}[]
   ]
 
id: 9; caller: []; line: 13; classic: false; kind: PRE; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&v!=0 & 1<=v' & x'=v+1 & v1'=1 & !(v2') & x'!=0 & x=x' & x!=0&
{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'!=0 & x!=0 & x=x' & !(v_bool_12_886') & x'!=0 & !(v_bool_12_886') & v_int_13_884'=1 & x'=v_int_13_948+1 & v_int_13_948!=0 & 1<=v_int_13_883' & v_int_13_948!=0&{FLOW,(24,25)=__norm}[]
   ]
 

id: 11; caller: []; line: 13; classic: false; kind: POST; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&res=v' & v'=v+1 & 1<=v & x'=0+1 & !(v1') & x'!=0 & x=x' & x!=0&
{FLOW,(24,25)=__norm}[]
 |-  emp&1<=res&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'!=0 & x!=0 & x=x' & !(v_bool_12_886') & x'!=0 & !(v_bool_12_886') & x'=0+1 & 1<=v_int_13_952 & 0=0 & v_int_13_885'=v_int_13_952+1 & res=v_int_13_885'&{FLOW,(24,25)=__norm}[]
   ]
 
id: 12; caller: []; line: 13; classic: false; kind: POST; hec_num: 2; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&res=v' & v'=v+1 & v1!=0 & 1<=v & x'=v1+1 & !(v1') & x'!=0 & x=x' & x!=0&
{FLOW,(24,25)=__norm}[]
 |-  emp&1<=res&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'!=0 & x!=0 & x=x' & !(v_bool_12_886') & x'!=0 & !(v_bool_12_886') & x'=v_int_13_948+1 & v_int_13_948!=0 & 1<=v_int_13_954 & v_int_13_948!=0 & v_int_13_885'=v_int_13_954+1 & res=v_int_13_885'&{FLOW,(24,25)=__norm}[]
   ]

*/


