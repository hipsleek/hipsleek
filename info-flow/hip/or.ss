int or1(int x, int z)
  requires ((z = 0 & x <^ @Lo) | (z != 0 & x <^ @Hi)) & z <^ @Lo
  ensures res <^ @Lo;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
int or2_fails(int x, int z)
  requires ((z = 0 & x <^ @Hi) | (z != 0 & x <^ @Lo)) & z <^ @Lo
  ensures res <^ @Lo;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
int or3_fails(int x, int z)
  requires ((z = 0 & x <^ @Hi) | (z != 0 & x <^ @Hi)) & z <^ @Lo
  ensures res <^ @Lo;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
int or4(int x, int z)
  requires ((z = 0 & x <^ @Lo) | (z != 0 & x <^ @Hi)) & z <^ @Lo
  ensures res <^ @Hi;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
int or5(int x, int z)
  requires ((z = 0 & x <^ @Hi) | (z != 0 & x <^ @Lo)) & z <^ @Lo
  ensures res <^ @Hi;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
int or6(int x, int z)
  requires ((z = 0 & x <^ @Hi) | (z != 0 & x <^ @Hi)) & z <^ @Lo
  ensures res <^ @Hi;
{
  if(z == 0) {
    return x;
  } else {
    return 0;
  }
}
