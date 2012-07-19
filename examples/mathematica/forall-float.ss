float foo()
  requires true
  ensures (forall (x: !(0.0 < x + 1.0 & x*x > 16.0)  | x >= res + 1.0));
{
  float r = 3.0;
  return r;
}


float bar()
  requires true
  ensures (forall (x: !(0.0 < x + 1.0 & x*x > 16.0)  | x >= res + 1.01));
{
  float r = 3.0;
  return r;
}
