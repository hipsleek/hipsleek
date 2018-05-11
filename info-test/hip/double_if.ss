int double_if1(int x)
  requires x<?@Lo
  ensures res<?@Lo;
{
  int y=0;
  int z=0;
  dprint;
  if(x == 0) {
    y = 1;
    dprint;
  }
  dprint;
  if(y == 0) {
    z = 1;
    dprint;
  }
  dprint;
  return z;
  dprint;
}

int double_if2(int x)
  requires x<?@Lo
  ensures res<?@Hi;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_if3_fail(int x)
  requires x<?@Hi
  ensures res<?@Lo;
{
  dprint;
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_if4(int x)
  requires x<?@Hi
  ensures res<?@Hi;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int double_ifS(int x)
  requires true
  ensures res<?x;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}
