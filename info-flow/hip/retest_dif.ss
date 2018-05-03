int dif1(int x)
  requires x<^@Lo
  ensures res<^@Lo;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  /* dprint; */
  if(y == 0) {
    z = 1;
  }
  /* dprint; */
  return z;
  dprint;
}

int dif2(int x)
  requires x<^@Lo
  ensures res<^@Hi;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int dif3f(int x)
  requires x<^@Hi
  ensures res<^@Lo;
{
  dprint;
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}

int dif4(int x)
  requires x<^@Hi
  ensures res<^@Hi;
{
  int y=0;
  int z=0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  return z;
}
