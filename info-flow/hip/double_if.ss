int double_if(int x)
  requires x <^ @Hi & (x = 0 | x = 1)
  ensures res <^ @Lo & res = x;
{
  int y = 0;
  int z = 0;
  if(x == 0) {
    dprint;
    y = 1;
  }
  if(y == 0) {
    dprint;
    z = 1;
  }
  dprint;
  return z;
}

int single_if(int x)
  requires x <^ @Hi & (x = 0 | x = 1)
  ensures res <^ @Hi & res = (1-x);
{
  int y = 0;
  if(x == 0) {
    dprint;
    y = 1;
  }
  return y;
}
