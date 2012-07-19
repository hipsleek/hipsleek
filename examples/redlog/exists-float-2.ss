float foo()
  requires true
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & 1/x < res);
{
  float r = 3.0;
  return r;
}


float bar()
  requires true
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & 1/x < res - 4);
{
  float r = 3.0;
  return r;
}
