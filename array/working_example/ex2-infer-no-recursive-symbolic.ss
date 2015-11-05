relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
{
  int k=5;
  int j=3;
  if (a[5]>0) {
    a[5] = a[k+1]-1;
    return a[6]; }
  else {
    k = k+1;
    return a[k]+1;
  }
}

