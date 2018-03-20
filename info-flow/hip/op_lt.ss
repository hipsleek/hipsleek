//////////////////////////////////////////////////
// ADDITION with constant
//////////////////////////////////////////////////
bool lt_constant_1(int x)
  requires x < 1 %% x <? @Lo
  ensures  res %% res <? @Lo;
{
  return x < 1;
}
bool lt_constant_2(int x)
  requires x < 1 %% x <? @Lo
  ensures  res %% res <? @Hi;
{
  return x < 1;
}
bool lt_constant_3_fail(int x)
  requires x < 1 %% x <? @Hi
  ensures  res %% res <? @Lo;
{
  return x < 1;
}
bool lt_constant_4(int x)
  requires x < 1 %% x <? @Hi
  ensures  res %% res <? @Hi;
{
  return x < 1;
}
bool lt_constant_S(int x)
  requires x < 1
  ensures  res %% res <? x;
{
  return x < 1;
}
//////////////////////////////////////////////////

//////////////////////////////////////////////////
// ADDITION with variables
//////////////////////////////////////////////////
bool lt_variable_1(int x, int y)
  requires x < 1 & y > 1 %% x <? @Lo & y <? @Lo
  ensures  res %% res <? @Lo;
{
  return x < y;
}
bool lt_variable_2(int x, int y)
  requires x < 1 & y > 1 %% x <? @Lo & y <? @Lo
  ensures  res %% res <? @Hi;
{
  return x < y;
}
bool lt_variable_3_fail(int x, int y)
  requires x < 1 & y > 1 %% x <? @Lo & y <? @Hi
  ensures  res %% res <? @Lo;
{
  return x < y;
}
bool lt_variable_4(int x, int y)
  requires x < 1 & y > 1 %% x <? @Lo & y <? @Hi
  ensures  res %% res <? @Hi;
{
  return x < y;
}
bool lt_variable_5_fail(int x, int y)
  requires x < 1 & y > 1 %% x <? @Hi & y <? @Lo
  ensures  res %% res <? @Lo;
{
  return x < y;
}
bool lt_variable_6(int x, int y)
  requires x < 1 & y > 1 %% x <? @Hi & y <? @Lo
  ensures  res %% res <? @Hi;
{
  return x < y;
}
bool lt_variable_7_fail(int x, int y)
  requires x < 1 & y > 1 %% x <? @Hi & y <? @Hi
  ensures  res %% res <? @Lo;
{
  return x < y;
}
bool lt_variable_8(int x, int y)
  requires x < 1 & y > 1 %% x <? @Hi & y <? @Hi
  ensures  res %% res <? @Hi;
{
  return x < y;
}
bool lt_variable_S(int x, int y)
  requires x < 1 & y > 1
  ensures  res %% res <? x |_| y;
{
  return x < y;
}
//////////////////////////////////////////////////
