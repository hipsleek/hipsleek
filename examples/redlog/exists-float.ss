float foo()
  requires true
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & x < res + 1.0);
{
  float r = 3.0;
  return r;
}


float bar()
  requires true
  ensures (exists x: x + 1.0 > 1.0 & x * x < 6.0  & x >= res + 1.0);
{
  float r = 3.0;
  return r;
}
