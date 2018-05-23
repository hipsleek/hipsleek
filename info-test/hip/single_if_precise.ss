int psingle_if1_safe(int x)
  requires (x=0|x=1) & x <? @Lo
  ensures res=(1-x) & res <? @Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int psingle_if2_safe(int x)
  requires (x=0|x=1) & x <? @Lo
  ensures res=(1-x) & res <? @Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int psingle_if3_fail(int x)
  requires (x=0|x=1) & x <? @Hi
  ensures res=(1-x) & res <? @Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int psingle_if4_safe(int x)
  requires (x=0|x=1) & x <? @Hi
  ensures res=(1-x) & res <? @Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int psingle_ifS_safe(int x)
  requires (x=0|x=1) & true
  ensures res=(1-x) & res <? x;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}
