int foo()
  requires true
  ensures res = (int)3.6;
{
  int x = (int) 3.2;
  return x;
}
