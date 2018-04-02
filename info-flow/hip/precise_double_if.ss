int double_if_1(int x)
  requires (x = 1 | x = 0) %% x <? @Lo
  ensures res = x %% res <? @Lo;
{
  int y = 1;
  int z = 1;
  if(x == 1) {
    y = 0;
  }
  if(y == 1) {
    z = 0;
  }
  return z;
}

int double_if_2(int x)
  requires (x = 1 | x = 0) %% x <? @Lo
  ensures res = x %% res <? @Hi;
{
  int y = 1;
  int z = 1;
  if(x == 1) {
    y = 0;
  }
  if(y == 1) {
    z = 0;
  }
  return z;
}

int double_if_3_fail(int x)
  requires (x = 1 | x = 0) %% x <? @Hi
  ensures res = x %% res <? @Lo;
{
  int y = 1;
  int z = 1;
  if(x == 1) {
    y = 0;
  }
  dprint;
  if(y == 1) {
    z = 0;
  }
  dprint;
  return z;
}

int double_if_4(int x)
  requires (x = 1 | x = 0) %% x <? @Hi
  ensures res = x %% res <? @Hi;
{
  int y = 1;
  int z = 1;
  if(x == 1) {
    y = 0;
  }
  if(y == 1) {
    z = 0;
  }
  return z;
}

int double_if_S(int x)
  requires (x = 1 | x = 0)
  ensures res = x %% res <? x;
{
  int y = 1;
  int z = 1;
  if(x == 1) {
    y = 0;
  }
  if(y == 1) {
    z = 0;
  }
  return z;
}
