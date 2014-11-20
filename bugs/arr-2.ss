void foo(int[] a, int i, ref int r)
{
  if (a[i] > 0) {
    a[i] = a[i] - 1;
    r++;
    foo(a, i, r);
  }
}
