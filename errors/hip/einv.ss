global int y =0;

int foo (int a, int b, int x)
  requires a=0 & b=-2 & x=1
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}
