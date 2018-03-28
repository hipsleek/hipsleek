//////////////////////////////////////////////////
// AUXILIARY DATA TYPE
//////////////////////////////////////////////////
data Cell {
  int val;
}

//////////////////////////////////////////////////
// BIND-GET CHECK with pure checking
//////////////////////////////////////////////////
int get1(Cell x)
  requires x::Cell<z+1> & true %% z <? @Lo & x <? @Lo
  ensures res = z+1 & true %% res <? @Lo;
{
  return x.val;
}

int get2(Cell x)
  requires x::Cell<z+1> & true %% z <? @Lo & x <? @Lo
  ensures res = z+1 & true %% res <? @Hi;
{
  return x.val;
}

int get3_fail(Cell x)
  requires x::Cell<z+1> & true %% z <? @Lo & x <? @Hi
  ensures res = z+1 & true %% res <? @Lo;
{
  return x.val;
}

int get4(Cell x)
  requires x::Cell<z+1> & true %% z <? @Lo & x <? @Hi
  ensures res = z+1 & true %% res <? @Hi;
{
  return x.val;
}

int get5_fail(Cell x)
  requires x::Cell<z+1> & true %% z <? @Hi & x <? @Lo
  ensures res = z+1 & true %% res <? @Lo;
{
  return x.val;
}

int get6(Cell x)
  requires x::Cell<z+1> & true %% z <? @Hi & x <? @Lo
  ensures res = z+1 & true %% res <? @Hi;
{
  return x.val;
}

int get7_fail(Cell x)
  requires x::Cell<z+1> & true %% z <? @Hi & x <? @Hi
  ensures res = z+1 & true %% res <? @Lo;
{
  return x.val;
}

int get8(Cell x)
  requires x::Cell<z+1> & true %% z <? @Hi & x <? @Hi
  ensures res = z+1 & true %% res <? @Hi;
{
  return x.val;
}
