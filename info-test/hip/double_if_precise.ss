int pdouble_if1_safe(int x)
  requires x<?#@Lo & (x=0|x=1)
  ensures res<?#@Lo & res=x;
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

int pdouble_if2_safe(int x)
  requires x<?#@Lo & (x=0|x=1)
  ensures res<?#@Hi & res=x;
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

int pdouble_if3_fail(int x)
  requires x<?#@Hi & (x=0|x=1)
  ensures res<?#@Lo & res=x;
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

int pdouble_if4_safe(int x)
  requires x<?#@Hi & (x=0|x=1)
  ensures res<?#@Hi & res=x;
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

int pdouble_ifS_safe(int x)
  requires (x=0|x=1)
  ensures res<?x & res=x;
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
