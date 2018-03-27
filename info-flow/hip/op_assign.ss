int assign_1(int x)
  requires x > 0 %% x <? @Lo
  ensures res > 0 %% res <? @Lo;
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_2(int x)
  requires x > 0 %% x <? @Lo
  ensures res > 0 %% res <? @Hi;
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_3_fail(int x)
  requires x > 0 %% x <? @Hi
  ensures res > 0 %% res <? @Lo;
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_4(int x)
  requires x > 0 %% x <? @Hi
  ensures res > 0 %% res <? @Hi;
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_S1(int x)
  requires x > 0
  ensures res > 0 %% res <? x;
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_S2(int x)
  requires x > 0
  ensures res > 0 %% res <? y';
{
  int y = x;
  x = x + 1;
  return y;
}

int assign_S3(int x)
  requires x > 0
  ensures res > 0 %% res <? y' |_| x;
{
  int y = x;
  x = x + 1;
  return y;
}
