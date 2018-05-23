int eq_branc(int x)
  requires x <E @Hi
  ensures res <E @Lo;
{
  int y;
  if(x > 0) {
    dprint;
    y = 2;
  } else {
    dprint;
    y = 1 + 1;
  }
  return y;
  dprint;
}
