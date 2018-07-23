func int tf(int m, int n) == ?.

int foo(int x, int y)
  requires x >= y ensures res = x;
  //requires x <= y ensures res = false;
{
  if (tf(x, y) > 0 ) {
     return x;
  } else {
     return y;
  }
}