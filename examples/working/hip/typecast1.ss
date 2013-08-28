int foo()
  requires true
  ensures res >= (int) 1.1;
{
  return 1;
}
