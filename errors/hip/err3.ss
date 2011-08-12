
//divbyzero
int foo(int x, int y)
  requires true
  ensures y=res*x;
{
  int a;
  a = y/x;
  return a;
}
