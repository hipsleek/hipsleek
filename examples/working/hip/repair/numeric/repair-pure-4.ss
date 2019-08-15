//func int tf(int m, int n) == ?.

int foo(int x, int y)
  requires true ensures res = x - 4 * y + 3;
{
  int a;
  a = x + 1;
  //a = 1 + tf(x,y);
  a = a + y;
  //a = a + tf(x, y);
  a = a + 1;
 // a = a + tf(x,y);
  return a;
}