//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a) ensures Q(res,a[5]);
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
# ex11a0.ss 

Add a flag --ignore-type-err for this. Otherwise should fail
by default.

ERROR: at ex11a0-infer-pre-post-arr-get.ss_8:33_8:34
Message: UNIFICATION ERROR : at location {(Line:8,Col:33),(Line:8,Col:34)} types int[] and int are inconsistent


*/
