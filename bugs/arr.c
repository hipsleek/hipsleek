void foo(int* a, int r)
{
  if (*a > 0) {
    *a--;
    r++;
    foo(a,r);
  }
}
