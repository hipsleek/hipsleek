int dif1(int x)
  requires x<^@Lo
  ensures res<^@Lo;
{
  int y=0;
  int z=0;
  dprint;
  if(x == 0) {
    y = 1;
    dprint;
  }
  dprint;
  if(y == 0) {
    z = 1;
    dprint;
  }
  dprint;
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

int difS(int x)
  requires true
  ensures res<^x;
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

int pdif1(int x)
  requires x<^@Lo & (x=0|x=1)
  ensures res<^@Lo & res=x;
{
  int y=0;
  int z=0;
  dprint;
  if(x == 0) {
    y = 1;
    dprint;
  }
  dprint;
  if(y == 0) {
    z = 1;
    dprint;
  }
  dprint;
  return z;
  dprint;
}

int pdif2(int x)
  requires x<^@Lo & (x=0|x=1)
  ensures res<^@Hi & res=x;
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

int pdif3f(int x)
  requires x<^@Hi & (x=0|x=1)
  ensures res<^@Lo & res=x;
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

int pdif4(int x)
  requires x<^@Hi & (x=0|x=1)
  ensures res<^@Hi & res=x;
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

int pdifS(int x)
  requires (x=0|x=1)
  ensures res<^x & res=x;
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
