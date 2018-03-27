int single_if_1(int x)
  requires true %% x <? @Lo
  ensures true %% res <? @Lo;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_2(int x)
  requires true %% x <? @Lo
  ensures true %% res <? @Hi;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_3_fail(int x)
  requires true %% x <? @Hi
  ensures true %% res <? @Lo;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_4(int x)
  requires true %% x <? @Hi
  ensures true %% res <? @Hi;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_S(int x)
  requires true
  ensures true %% res <? x;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}
