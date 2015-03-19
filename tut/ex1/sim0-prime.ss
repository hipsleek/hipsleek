// pass-by-value parameter x
// x' is the current value of variable x
// x  is orig value at start of method


int foo(int x)
  requires true
  ensures res=x+2;
{
  x=x+1;
  assert x'=x+1;
  int r =x+1;
  assert r'=x+2;
  assert r'=x'+1;
  return r;
}

