func int tf(int m, int n) == ?.
func int tf3(int m) == ?.

int foo(int x, int y)
    //requires true ensures res = a;
   requires x > y ensures res = x;
  requires x <= y ensures res = y;
  // requires true ensures case {
  //    x >= y -> [] res = x;
  //    x < y -> [] res = y;
  // };
{
  //if (tf(x, y) > 0 ) {
  int a;
  if (x - y > 0) {
     a = tf3(x);
  } else {
     a = y;
  }

  return a;
}