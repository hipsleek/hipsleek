//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P(int a,int b,int r).
relation P1(int a,int b).
relation P2(int[] a,int[] b).

void loop(ref int[] a)
  infer[P1,P2] //@arr_elems
  requires true
//ensures P1(a[5],a'[5]);
  ensures P2(a,a');
{
  if (a[5]>0) {
     a[5] = a[5] -1;
    return loop(a);
  }
}

/*

// using P2
[RELDEFN P2: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P2(a_1225,a')) -->  P2(a,a'),
RELDEFN P2: ( a'[5]=a[5] & (a[5])<=0) -->  P2(a,a')]

 
id: 12; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ P1,P2]; c_heap: emp
 checkentail 
(exists a_1223: htrue&res=v_void_17_1168' & P2(a_1223,a') & 
 update_array_1d(a,a_1223,v_int_16_1222,5) & v_int_16_1222+1=a[5] & 
 0<(a[5]) & v_bool_15_1169' &{FLOW,(4,5)=__norm#E}[]
 |-  emp&P2(a,a') &{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN P2: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P2(a_1225,a')) -->  P2(a,a')]
ho_vars: nothing?
res:  1[
   htrue&res=v_void_17_1168' & P2(a_1225,a') & update_array_1d(a,a_1225,v_int_16_1222,5) & v_int_16_1222+1=a[5] & 0<(a[5]) & v_bool_15_1169'&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [P1; P2]
   es_infer_rel: [RELDEFN P2: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P2(a_1225,a')) -->  P2(a,a')]
   ]


// using P1
[RELDEFN P1: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P1(a_1225[5],a'[5])) -->  P1(a[5],a'[5]),
RELDEFN P1: ( a'[5]=a[5] & (a[5])<=0) -->  P1(a[5],a'[5])]

id: 12; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ P1,P2]; c_heap: emp
checkentail 
 (exists a_1223: htrue&res=v_void_17_1168' & P1(a_1223[5],a'[5]) & 
 update_array_1d(a,a_1223,v_int_16_1222,5) & v_int_16_1222+1=a[5] & 
 0<(a[5]) & v_bool_15_1169'  &{FLOW,(4,5)=__norm#E}[]
 |-  emp&P1(a[5],a'[5])&{FLOW,(4,5)=__norm#E}[]. 
pure rel_ass: [RELDEFN P1: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P1(a_1225[5],a'[5])) -->  P1(a[5],a'[5])]
ho_vars: nothing?
res:  1[
   htrue&res=v_void_17_1168' & P1(a_1225[5],a'[5]) & update_array_1d(a,a_1225,v_int_16_1222,5) & v_int_16_1222+1=a[5] & 0<(a[5]) & v_bool_15_1169'&{FLOW,(4,5)=__norm#E}[]
   es_infer_vars/rel/templ: [P1; P2]
   es_infer_rel: [RELDEFN P1: ( a_1225[5]=(a[5])-1 & true & 1<=(a[5]) & P1(a_1225[5],a'[5])) -->  P1(a[5],a'[5])]
   ]



*/
