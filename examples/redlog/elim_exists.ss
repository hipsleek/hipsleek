int foo(int r)
  requires true 
  ensures (exists x: res = x & x = 1);
{
  r = 1;
  return r;
}

int bar()
  requires true
  ensures (exists x: 0 < x < 3 & res - x = 1);
{
  int r = 3;
  return r;
}

int goo()
  requires true
  ensures (exists x: 0 < x + 1 & 2*x < 6  & res - x = 1);
{
  int r = 3;
  return r;
}
