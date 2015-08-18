pred_prim read<b:bag(int)>;

//pred_prim read<b:int>;

int read_arr(int[] a, int i)
  requires a::read<J>@L & J={i}
  ensures  res=a[i];

int foo2(int[] a)
  requires a::read<{5}>@L
  ensures res=a[5]+6;
{
  int v=read_arr(a,5);
  return v+6;
}

/*
# ex8a3.ss -tp oc --ato

# reading only

id: 0; caller: []; line: 13; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@dis_err]
 
checkentail (exists flted_10_38: a::read<flted_10_38>@L&
v_int_13_1387'=5 & flted_10_38={5} & a'=a & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists flted_6_40: a'::read<flted_6_40>@L&
flted_6_40={j_1409} & j_1409=v_int_13_1387'&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?

*/
