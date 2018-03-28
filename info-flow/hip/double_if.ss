//////////////////////////////////////////////////
// DOUBLE-IF CHECK without pure checking
//////////////////////////////////////////////////
int double_if_1(int x)
  requires true %% x <? @Lo
  ensures true %% res <? @Lo;
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
  requires true %% x <? @Lo
  ensures true %% res <? @Hi;
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
  requires true %% x <? @Hi
  ensures true %% res <? @Lo;
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

int double_if_4(int x)
  requires true %% x <? @Hi
  ensures true %% res <? @Hi;
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
  requires true
  ensures true %% res <? x;
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
