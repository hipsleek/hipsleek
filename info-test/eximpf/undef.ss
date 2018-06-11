int undef1_safe()
  requires true
  ensures res <E @Lo;
{
  int v;
  return v;
}

int undef2_safe()
  requires true
  ensures res <E @Hi;
{
  int v;
  return v;
}
