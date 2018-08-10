int foo(int x, int y)
/*@ requires true ensures res = 2 * x + y + 3; */
{
  int a;
  a = x + 1;
  a = a + y;
  a = a + 1;
  return a;
}
