//////////////////////////////////////////////////
// COMPLEX OPERATION
//////////////////////////////////////////////////
int add(int x, int y, int z)
  requires true
  ensures  res=x+y+z %% res <? x |_| y |_| z;
{
  return x + y + z;
}
int sub(int x, int y, int z)
  requires true
  ensures  res=x-y-z %% res <? x |_| y |_| z;
{
  return x - y - z;
}
int mul(int x, int y, int z)
  requires true
  ensures  res=x*y*z %% res <? x |_| y |_| z;
{
  return x * y * z;
}

int foo(int x, int y, int z, int w)
  requires true
  ensures  res=x+y-z*w %% res <? x |_| y |_| z |_| w;
{
  return x + y - z * w;
}

int add_fail(int x, int y, int z)
  requires true
  ensures  res=x+y+z %% res <? y |_| z;
{
  return x + y + z;
}
int sub_fail(int x, int y, int z)
  requires true
  ensures  res=x+y+z %% res <? x |_| z;
{
  return x - y - z;
}
int mul_fail(int x, int y, int z)
  requires true
  ensures  res=x*y*z %% res <? x |_| y;
{
  return x * y * z;
}

int foo_fail(int x, int y, int z, int w)
  requires true
  ensures  res=x+y-z*w %% res <? x |_| y |_| z;
{
  return x + y - z * w;
}
//////////////////////////////////////////////////
