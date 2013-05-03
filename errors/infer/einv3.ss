global int y =0;

int foo (int a, int b, int x)
  requires true
  ensures res>=0;
{
  x = x+a;
  x=0;
  x= x+b;
  y = y + a;
  return x;
}

relation H1(int a, int b, int c).
/*
[RELASS [H1]: ( H1(a,b,x)) -->  0<=(b+a+x)]
 */
int foo1 (int a, int b, int x)
  infer[H1]
  requires H1(a,b,x)
  ensures res>=0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}

relation H2(int a, int b, int c).

/*
[RELASS [H2]: ( H2(a,b,x)) -->  (b+a+x)<0]
*/
int foo2 (int a, int b, int x)
  infer[H2]
  requires H2(a,b,x)
  ensures res<0;
{
  x = x+a;
  x= x+b;
  y = y + a;
  return x;
}
