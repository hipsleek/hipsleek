int foo()
  requires true
  ensures (forall (x: !(0 < x + 1 & x*x >= 16)  | x >= res + 1));
{
  int r = 3;
  return r;
}


int bar()
  requires true
  ensures (forall (x: !(0 < x + 1 & x*x >= 16)  | x > res + 1));
{
  int r = 3;
  return r;
}
