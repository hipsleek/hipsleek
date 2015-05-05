//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
  relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  a[5]=10;
  return a[4];
}

/*
# ex11d.ss 

id: 4; caller: []; line: 0; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ P,Q]; c_heap: emp; others: [@arrvar] globals: [@flow,@ver_post]
 checkentail emp&res=v_int_12_1157' & v_int_12_1157'=a'[4] & 
update_array_1d(a,a',10,5) & P(a) & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  emp&Q(a,a',res)&{FLOW,(4,5)=__norm#E}[]. 



*/
