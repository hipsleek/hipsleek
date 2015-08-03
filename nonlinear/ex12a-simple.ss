
int mult(int x, int y)
  requires true
  ensures res=x*y;

int foo(int xxx)
  requires true
  ensures res=2*xxx;
{
  int t = mult(xxx,2);
  return t;
}

/*
int foo2(int x,int y)
  requires true
  ensures res=x*y;
{
  int t = mult(x,y);
  return t;
}
*/

