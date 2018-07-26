//func int tf(int m, int n) == ?.
//func int tf3(int m) == ?.

int foo(int x, int y)
   requires x > y ensures res = x + 2;
   requires x <= y ensures res = y + 2;
{
  int a;
  if (x - y  <= 0 ) {
     a = x;
  } else {
     a = y;
  }

  return a + 2;
}
