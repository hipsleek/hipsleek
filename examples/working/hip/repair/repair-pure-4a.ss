//func int tf2(int x,int y) == ?.
//func int tf3(int x) == ?.

int foo(int x, int y)
  requires true ensures res = x + y + 3;
{
  int a;
  a = x + 1;
  //a = x + 3;
  //a = tf3(x);
  a = a + y;
  a = a + 1;  
//  a = tf2(a,y);
  return a;
}