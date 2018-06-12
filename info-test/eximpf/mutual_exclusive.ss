int mutual1_safe(int x)
  requires x <E @Lo
  ensures res=1 & res <E @Lo;
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
  requires x <E @Lo
  ensures res=1 & res <E @Hi;
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
  requires x <E @Hi & (x=0|x=1)
  ensures res=1 & res <E @Lo;
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
  requires x <E @Hi
  ensures res=1 & res <E @Hi;
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




int mutual_plus1_safe(int x)
  requires x <E @Lo
  ensures res=1 & res <E @Lo;
{
  int y;
  if(x == 0) {
    y = 2;
  }
  if(x != 0) {
    y = 1+1;
  }
  return y;
}

int mutual_plus2_safe(int x)
  requires x <E @Lo
  ensures res=1 & res <E @Hi;
{
  int y;
  if(x == 0) {
    y = 2;
  }
  if(x != 0) {
    y = 1+1;
  }
  return y;
}

int mutual_plus3_safe(int x)
  requires x <E @Hi & (x=0|x=1)
  ensures res=1 & res <E @Lo;
{
  int y;
  if(x == 0) {
    y = 2;
  }
  if(x != 0) {
    y = 1+1;
  }
  return y;
}

int mutual_plus4_safe(int x)
  requires x <E @Hi
  ensures res=1 & res <E @Hi;
{
  int y;
  if(x == 0) {
    y = 2;
  }
  if(x != 0) {
    y = 1+1;
  }
  return y;
}
