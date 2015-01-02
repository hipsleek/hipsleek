// pass-by-value parameters

int foo(int x)
  requires true
  ensures res=x+2;
{
  x=x+1;
  return x+1;
}

int main()
  requires true
  ensures res=10;
{
  int xx=10;
  int r = foo(xx);
  assert r'=12;
  assert xx'=10;
  return xx;
}
