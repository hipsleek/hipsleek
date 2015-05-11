//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P(int a,int b,int r).
relation P1(int a,int b).
relation P2(int[] a,int[] b).

void loop(ref int[] a)
  infer[P1,P2]
  requires true
//ensures P1(a[5],a'[5]);
  ensures P2(a,a'[5]);
{
  if (a[5]>0) {
     a[5] = a[5] -1;
    return loop(a);
  }
}


/* 
# ex24a 

should be a type-error and then just FAIL..

ERROR: at ex24a-array-recursive-type-err.ss_13:15_13:20
Message: UNIFICATION ERROR : at location {(Line:13,Col:15),(Line:13,Col:20)} types int[] and int[][] are in
consistent


*/
