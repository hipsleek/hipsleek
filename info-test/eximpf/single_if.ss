int single_if1_safe(int x)
  requires x <E #@Lo
  ensures res <E #@Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if2_safe(int x)
  requires x <E #@Lo
  ensures res <E #@Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if3_fail(int x)
  requires x <E #@Hi
  ensures res <E #@Lo;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_if4_safe(int x)
  requires x <E #@Hi
  ensures res <E #@Hi;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}

int single_ifS_safe(int x)
  requires true
  ensures res <E x;
{
  int y=0;
  if(x == 0) {
    y = 1;
  }
  return y;
}
