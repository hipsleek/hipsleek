//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a[6]>0) {
    a[5] = 7;
  } 
  else {
    a[5] = 8;
  }
  return a[5];
}
