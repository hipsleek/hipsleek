func int tf2(int x,int y) == ?.
//func int tf3(int x) == ?.

int foo(int x, int y)
  requires true ensures res = x + y + 3;
{
  int a;
  a = tf2(x, y);
  return a;
}

//int foo2(int x)                
//   requires true ensures res = x + 3;
// {
//   int a;
//   a = tf3(x);
//   return a;
// }


//relation dom(int x, int y) == true.
//a = x + y;

//func int tf3(int x) == ?.
// int f2(int x, int y)
//   requires true ensures res = x + y + 3;
// {
//     return x + y + 3;
// }