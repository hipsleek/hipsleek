//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a[5]) ensures Q(res,a[5]);
//  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  if (a[5]>10) {
    return a[5];
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11a.ss

Should fail when there is a type error;
unless we have ignore-type-error flag.

ERROR: at ex11a-infer-pre-post-arr-get.ss_8:33_8:34
Message: UNIFICATION ERROR : at location {(Line:8,Col:33),(Line:8,Col:34)} types int[] and int are inconsistent

Last Proving Location: ex11a-infer-pre-post-arr-get.ss_6:0_0:-1

ERROR: at ex11a-infer-pre-post-arr-get.ss_8:33_8:34
Message: gather_type_info_var : unexpected exception Failure("UNIFICATION ERROR : at location {(Line:8,Col:33),(Line:8,Col:34)} types int[] and int are inconsistent")
gather_type_info_b_formula: relation P


 */
