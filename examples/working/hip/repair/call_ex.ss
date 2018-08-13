func int tf(int k) == ?.

int sum(int a, int b)
    requires true ensures res = a + b;
{
  return a + b;
}

int foo(int x, int y)
    requires x > y ensures res = 2 * x + y;
{
  if (x > y) {
     int k;
     k = sum(x, y);
     return x - tf(k);
  }
  return y;
}