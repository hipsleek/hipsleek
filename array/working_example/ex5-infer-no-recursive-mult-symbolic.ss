relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
{
  int k=5;
  int j=3;
  if (a[k]>0) {
    a[k] = a[k]-1;
    return a[k]; }
  else {
    a[j] = a[j]+1;
    return a[j];
  }
}


/*

*************************************
******pure relation assumption*******
*************************************
[RELDEFN Q: ( update_array_1d(a_1263,a_1272,v_int_18_1262,5) & v_int_18_1262=(a_1263[5])-
1 & 1<=(a[5]) & Q(a_1272,a',res) & update_array_1d(a,a_1263,1+(a[4]),4)) -->  Q(a,a',res),
RELDEFN Q: ( a[4]=res & a'[4]=res & a'=a & (a'[5])<=0) -->  Q(a,a',res)]
*************************************

Post Inference result:
foo$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a]
           emp&(((a[5])>=1 & a'[4]=res & a'[4]=(a[4])+(a[5]) & 0=a'[5]) | 
           (0>=(a'[5]) & a[4]=res & a=a'))&{FLOW,(4,5)=__norm#E}[]

*/

