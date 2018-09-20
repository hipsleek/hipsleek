
global int y = 1;


/*
int foo1(int x)
 requires y>1
 ensures  res=y+x & y'=y+1;

{
  int t = y;
  y = y + 1;
  return x + t;
}

*/

int foo2(int x)
 requires true
 ensures  res=2;
{
  return y;
}

void main()
{
 dprint;
 y = y + 1;
 dprint;
}
