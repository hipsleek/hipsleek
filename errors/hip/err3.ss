//./hip errors/hip/err3.ss -tp redlog
//VALID
int foo1(int x, int y)
  requires y>0 & x > 1
  ensures true;
{
  return y/x;
}

//divbyzero
//MAY: LOC[11;12; 15]
int foo5(int x, int y)
  requires y>0 & x > -3
  ensures true;
{
  return y/x;
}

//divbyzero
//MUST: LOC[20; 21; 24]
int foo6(int x, int y)
  requires y>0 & x =0
  ensures true;
{
  return y/x;
}

//MAY: LOC[28;29;32]
int foo2(int x, int y)
  requires y>0
  ensures true;
{
  int z = y/x;
  return z;
}

//MAY: LOC[37;38;42;43]
int foo3(int x, int y)
  requires y>0 & x>0
  ensures true;
{
  int z =0;
  z = x-2;
  z = y/z;
  return z;
}

//MAY: LOC[48;49;53;54]
int foo4(int x, int y)
  requires y>0
  ensures true;
{
  int z =0;
  z = x-2;
  z = y/z;
  return z;
}

//VALID
int foo7(int x, int y)
  requires y>0
  ensures true;
{
  int z =0;
  x = 1;
  z = x-2;
  z = y/z;
  return z;
}
