int mutual1_safe(int x)
  requires x <? #@Lo
  ensures res=1 & res <? #@Lo;
{
  int y;
  if(x == 0) {
    y = 1;
  }
  if(x != 0) {
    y = 1;
  }
  return y;
}

int mutual2_safe(int x)
  requires x <? #@Lo
  ensures res=1 & res <? #@Hi;
{
  int y;
  if(x == 0) {
    y = 1;
  }
  if(x != 0) {
    y = 1;
  }
  return y;
}

int mutual3_safe(int x)
  requires x <? #@Hi
  ensures res=1 & res <? #@Lo;
{
  int y;
  if(x == 0) {
    y = 1;
  }
  if(x != 0) {
    y = 1;
  }
  return y;
}

int mutual4_safe(int x)
  requires x <? #@Hi
  ensures res=1 & res <? #@Hi;
{
  int y;
  if(x == 0) {
    y = 1;
  }
  if(x != 0) {
    y = 1;
  }
  return y;
}
