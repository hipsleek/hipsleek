int pdouble_if1_safe(int x)
  requires x <E #@Lo & (x=0|x=1)
  ensures res <E #@Lo & res=x;
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
  requires x <E #@Lo & (x=0|x=1)
  ensures res <E #@Hi & res=x;
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
  requires x <E #@Hi & (x=0|x=1)
  ensures res <E #@Lo & res=x;
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
  requires x <E #@Hi & (x=0|x=1)
  ensures res <E #@Hi & res=x;
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
  ensures res <E x & res=x;
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
