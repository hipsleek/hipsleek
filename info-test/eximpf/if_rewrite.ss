int if_rewrite1_safe(int x, int y)
  requires x <E @Lo & y <E @Lo
  ensures res <E @Lo;
{
  int z = 0;
  if(y == 0) {
    z = 1;
    y = x;
  } else {
    z = 2;
    y = x;
  }
  return z;
}

int if_rewrite2_safe(int x, int y)
  requires x <E @Lo & y <E @Lo
  ensures res <E @Hi;
{
  int z = 0;
  if(y == 0) {
    z = 1;
    y = x;
  } else {
    z = 2;
    y = x;
  }
  return z;
}

int if_rewrite3_safe(int x, int y)
  requires x <E @Hi & y <E @Lo
  ensures res <E @Lo;
{
  int z = 0;
  if(y == 0) {
    z = 1;
    y = x;
  } else {
    z = 2;
    y = x;
  }
  return z;
}

int if_rewrite4_safe(int x, int y)
  requires x <E @Hi & y <E @Lo
  ensures res <E @Hi;
{
  int z = 0;
  if(y == 0) {
    z = 1;
    y = x;
  } else {
    z = 2;
    y = x;
  }
  return z;
}
