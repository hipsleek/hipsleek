global int a;
global int b;

bool foo1()
  requires (a < b) ensures res = true;
  requires (a >= b) ensures res = false;
{
  return (a - b <= 0);
}

bool foo2()
  requires (a < b) ensures res = true;
  requires (a >= b) ensures res = false;
{
  return (a - b <= 0);
}
