int foo()
  requires true
  ensures (exists x: x + 1 > 1 & x * x < 6  & x < res + 1);
{
  int r = 3;
  return r;
}


int bar()
  requires true
  ensures (exists x: x + 1 > 1 & x * x < 6 & x >= res + 1);
{
  int r = 3;
  return r;
}
