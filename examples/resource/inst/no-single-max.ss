include "stack.ss"

bool rand()
 requires true
 ensures res or !res;

int g() 
  requires true
  ensures  res=1;
{
  return 1;
}


int h() 
  requires true
  ensures  res=2;
{
  int x=g();
  return x+1;
}


int f() 
  requires true
  ensures  res=3;
{

  int r=g();
  r = r+h();
  return r;
}


