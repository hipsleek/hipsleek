int single_if1_safe(int x)
  requires x <? #@Lo
  ensures res <? #@Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if2_safe(int x)
  requires x <? #@Lo
  ensures res <? #@Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if3_fail(int x)
  requires x <? #@Hi
  ensures res <? #@Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if4_safe(int x)
  requires x <? #@Hi
  ensures res <? #@Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_ifS_safe(int x)
  requires true
  ensures res <? x;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}
