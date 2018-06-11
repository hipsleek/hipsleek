int undef1_safe()
  requires true
  ensures res <? @Lo;
{
  int v;
  return v;
}

int undef2_safe()
  requires true
  ensures res <? @Hi;
{
  int v;
  return v;
}
