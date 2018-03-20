//////////////////////////////////////////////////
// ADDITION with constant
//////////////////////////////////////////////////
int add_constant_1(int x)
  requires true %% x <? @Lo
  ensures  res = x + 1 %% res <? @Lo;
{
  return x + 1;
}
int add_constant_2(int x)
  requires true %% x <? @Lo
  ensures  res = x + 1 %% res <? @Hi;
{
  return x + 1;
}
int add_constant_3_fail(int x)
  requires true %% x <? @Hi
  ensures  res = x + 1 %% res <? @Lo;
{
  return x + 1;
}
int add_constant_4(int x)
  requires true %% x <? @Hi
  ensures  res = x + 1 %% res <? @Hi;
{
  return x + 1;
}
int add_constant_S(int x)
  requires true
  ensures  res = x + 1 %% res <? x;
{
  return x + 1;
}
//////////////////////////////////////////////////

//////////////////////////////////////////////////
// ADDITION with variables
//////////////////////////////////////////////////
int add_variable_1(int x, int y)
  requires true %% x <? @Lo & y <? @Lo
  ensures  res = x + y %% res <? @Lo;
{
  return x + y;
}
int add_variable_2(int x, int y)
  requires true %% x <? @Lo & y <? @Lo
  ensures  res = x + y %% res <? @Hi;
{
  return x + y;
}
int add_variable_3_fail(int x, int y)
  requires true %% x <? @Lo & y <? @Hi
  ensures  res = x + y %% res <? @Lo;
{
  return x + y;
}
int add_variable_4(int x, int y)
  requires true %% x <? @Lo & y <? @Hi
  ensures  res = x + y %% res <? @Hi;
{
  return x + y;
}
int add_variable_5_fail(int x, int y)
  requires true %% x <? @Hi & y <? @Lo
  ensures  res = x + y %% res <? @Lo;
{
  return x + y;
}
int add_variable_6(int x, int y)
  requires true %% x <? @Hi & y <? @Lo
  ensures  res = x + y %% res <? @Hi;
{
  return x + y;
}
int add_variable_7_fail(int x, int y)
  requires true %% x <? @Hi & y <? @Hi
  ensures  res = x + y %% res <? @Lo;
{
  return x + y;
}
int add_variable_8(int x, int y)
  requires true %% x <? @Hi & y <? @Hi
  ensures  res = x + y %% res <? @Hi;
{
  return x + y;
}
int add_variable_S(int x, int y)
  requires true
  ensures  res = x + y %% res <? x |_| y;
{
  return x + y;
}
//////////////////////////////////////////////////
