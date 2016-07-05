int foo(int a)
  requires a = 3
  ensures res = 1;
{
  return a/2;
}

int val(int a)
  requires 0 < a < 3 
  ensures (res = 1 | res = 2);
{
  return a;
}

int mid(int a, int b)
  requires a < b
  ensures a <= res < b;
{
  return (a+b)/2;
}

int even(int a)
  requires true
  ensures (exists x: res = 2*x);
{
  return a+1;
}
