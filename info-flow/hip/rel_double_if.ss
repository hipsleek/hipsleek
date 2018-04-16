int double_if_1(int x)
  requires (x=0|x=1) & x<?@Lo
  ensures res=x & res<?@Lo;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_if_2(int x)
  requires (x=0|x=1) & x<?@Lo
  ensures res=x & res<?@Hi;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_if_3_fail(int x)
  requires (x=0|x=1) & x<?@Hi
  ensures res=x & res<?@Lo;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_if_4(int x)
  requires (x=0|x=1) & x<?@Hi
  ensures res=x & res<?@Hi;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  dprint;
  return z;
}

int double_if_S(int x)
  requires (x=0|x=1) & x<?@Hi
  ensures res=x & res<?x;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}
