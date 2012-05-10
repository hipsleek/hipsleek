

void foo()
requires true
  ensures true;
{
  int[] a;
  assume dom(a, 0, 4);

  return;
}
