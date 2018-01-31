int if1(int x)
  requires x <^ @Lo
  ensures res <^ @Lo;
{
  if(x == 0) {
    return 0;
  }
  return 1;
}
int if2_fails(int x)
  requires x <^ @Hi
  ensures res <^ @Lo;
{
  if(x == 0) {
    return 0;
  }
  return 1;
}
int if3(int x)
  requires x <^ @Lo
  ensures res <^ @Hi;
{
  if(x == 0) {
    return 0;
  }
  return 1;
}
int if4(int x)
  requires x <^ @Hi
  ensures res <^ @Hi;
{
  if(x == 0) {
    return 0;
  }
  return 1;
}

