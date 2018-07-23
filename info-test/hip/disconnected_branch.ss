int disconnect1_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Lo
  ensures res <? @Lo;
{
  int w = 0;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect2_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Lo
  ensures res <? @Hi;
{
  int w = 0;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect3_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Hi
  ensures res <? @Lo;
{
  int w = 0;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect4_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Hi
  ensures res <? @Hi;
{
  int w = 0;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}


int disconnect_undef1_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Lo
  ensures res <? @Lo;
{
  int w;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect_undef2_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Lo
  ensures res <? @Hi;
{
  int w;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect_undef3_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Hi
  ensures res <? @Lo;
{
  int w;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}

int disconnect_undef4_safe(int x, int y, int z)
  requires y <? @Lo & z <? @Lo & x <? @Hi
  ensures res <? @Hi;
{
  int w;
  if(y > 0) {
    z = x;
  }
  if(y <= 0) {
    w = z;
  }
  return w;
}
