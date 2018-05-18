
int _if(int x)
  requires x <? @Hi
  ensures res <? @Lo;
{
  int y;
  if(x == 0) {
    y = 1;
  } else {
    y = 2;
  }
  dprint;
  return y;
}
