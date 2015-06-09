relation P(int[] a).
relation Q(int[] a,int[] b,int r).
int foo(ref int[] a)
   infer [@arrvar,P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);
{
   a[5]=10;
   return a[4];
}
