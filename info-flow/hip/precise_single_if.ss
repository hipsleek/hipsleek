//////////////////////////////////////////////////
// SINGLE-IF CHECK with pure checking
//////////////////////////////////////////////////
int single_if_1(int x)
  requires (x=0|x=1) %% x <? @Lo
  ensures res=x %% res <? @Lo;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_2(int x)
  requires (x=0|x=1) %% x <? @Lo
  ensures res=x %% res <? @Hi;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_3_fail(int x)
  requires (x=0|x=1) %% x <? @Hi
  ensures res=x %% res <? @Lo;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_4(int x)
  requires (x=0|x=1) %% x <? @Hi
  ensures res=x %% res <? @Hi;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}

int single_if_S(int x)
  requires (x=0|x=1)
  ensures res=x %% res <? x;
{
  if(x == 1) {
    return 1;
  } else {
    return 0;
  }
}
