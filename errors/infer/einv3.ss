global int y =0;

int foo (int a, int b, int x)
  requires true
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}

