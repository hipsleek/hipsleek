
int fact(int x)
  requires true
  ensures res>=1;
  //requires true
  //ensures true;
  /*  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost();
  }
  */
{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}

/*
# fact2.ss

--dis-print-tidy

id: 2; caller: []; line: 15; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&x'=x & x'!=0 & !(v_bool_14_1111') & x'!=0 & !(v_bool_14_1111') & 
v_int_15_1109'=1 & v_int_15_1106'=1&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&x'=x & x'!=0 & !(v_bool_14_1111') & x'!=0 & !(v_bool_14_1111') & v_int_15_1109'=1 & v_int_15_1106'=1&{FLOW,(24,25)=__norm}[]
   ]

(i) remove duplicates
(ii) keep x'=x



id: 2; caller: []; line: 15; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: []; c_heap: emp
 checkentail emp&x!=0 & !(v4') & v3'=1 & v2'=1&{FLOW,(24,25)=__norm}[]
 |-  emp&{FLOW,(24,25)=__norm}[]. 
res:  1[
   emp&v2'=1 & v3'=1 & !(v4') & x!=0&{FLOW,(24,25)=__norm}[]
   ]


From hip,
   v_type_lno_?
From hip/sleek
   flted_?


*/
