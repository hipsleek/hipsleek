
//divbyzero
int foo(int x, int y)
  requires y>0
  ensures y=res*x;
{
  dprint;
  return y/x;
}
