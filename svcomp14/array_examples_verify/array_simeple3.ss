void foo2(ref int[] a)
  requires true
  ensures (a[5]>0 & a'[5]=0) | (a[5]<=0 & a'[5]=a[5]);
{
  if (a[5]>0) {
    a[5] = 0;
    foo2(a);
  }
}
