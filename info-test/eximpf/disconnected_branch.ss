int disconnect1_safe(int x, int y, int z)
  requires y <E @Lo & z <E @Lo & x <E @Lo
  ensures res <E @Lo;
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
  requires y <E @Lo & z <E @Lo & x <E @Lo
  ensures res <E @Hi;
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
  requires y <E @Lo & z <E @Lo & x <E @Hi
  ensures res <E @Lo;
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
  requires y <E @Lo & z <E @Lo & x <E @Hi
  ensures res <E @Hi;
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
