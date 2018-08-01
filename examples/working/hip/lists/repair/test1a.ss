global int var_x;
global int var_y;

int sum()
requires true ensures res = var_x + var_y;
{
   return var_x + var_y;
}

bool foo(int z)
requires z >= var_x + var_y ensures res = true;
{
  bool r;
  int a;
  r = (z > sum());
  return r;
}
