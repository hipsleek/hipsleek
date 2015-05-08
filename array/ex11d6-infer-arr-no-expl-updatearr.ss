//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
  relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
  infer [P,Q//,update_array_1d
    ] requires P(a) ensures Q(a,a',res);
{
  a[5]=10;
  return a[4];
}

/*
# ex11d6.ss 

int foo(ref int[] a)
  infer [P,Q//,update_array_1d
    ] requires P(a) ensures Q(a,a',res);

# without arrvar, without explicit update_arr.

[RELDEFN Q: ( exists(v_int_11_1157':res=v_int_11_1157' & v_int_11_1157'=a'[4]) & P(a)) -->  Q(a,a',res)]

We may need to distinguish unknown relation from interpreted relation
like update_arr by adding such interpreted relation into system.

*/
