
//divbyzero
//MAY: LOC[8; 5]
int foo1(int x, int y)
  requires y>0
  ensures true;
{
  return y/x;
}

//MAY: LOC[16; 13]
int foo2(int x, int y)
  requires y>0
  ensures true;
{
  int z = y/x;
  return z;
}

//MAY: LOC[27;26; 22]
int foo3(int x, int y)
  requires y>0 & x>0
  ensures true;
{
  int z =0;
  z = x-2;
  z = y/z;
  return z;
}

//MAY: LOC[39;38; 37]
int foo4(int x, int y)
  requires y>0
  ensures true;
{
  int z =0;
  x = 1;
  z = x-2;
  z = y/z;
  return z;
}
