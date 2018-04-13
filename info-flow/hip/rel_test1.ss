int id(int x)
  requires true
  ensures res = x & res <? x;
{
  return x;
  dprint;
}

int one()
  requires true
  ensures res=1 & res<?@Lo;
{
  return 1;
  dprint;
}

int inc(int x)
  requires true
  ensures res = x+1 & res <? x;
{
  int z = 1;
  return x+z;
  dprint;
}

int inc_fail(int x)
  requires true
  ensures res = x+1 & res <? @Lo;
{
  return x+1;
  dprint;
}

bool orf(bool x)
  requires true
  ensures res & res<?x;
{
  return x||true;
  dprint;
}

int add(int x, int y)
  requires true
  ensures res=x+y & res<?x%y;
{
  dprint;
  return x+y;
  dprint;
}
int addX_fail(int x, int y)
  requires true
  ensures res=x+y & res<?x;
{
  dprint;
  return x+y;
  dprint;
}
int addY_fail(int x, int y)
  requires true
  ensures res=x+y & res<?y;
{
  dprint;
  return x+y;
  dprint;
}
