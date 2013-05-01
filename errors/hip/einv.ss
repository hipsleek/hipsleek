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

relation H(int a, int b, int c).

/*
H(a,b,x)) -->  0<=(x+a+b)
*/
int goo (int a, int b, int x)
  infer [H]
  requires H(a, b, x)
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}
