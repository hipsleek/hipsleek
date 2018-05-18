int equal_branch1_safe(int x)
  requires x <E @Lo
  ensures res <E @Lo;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branch2_safe(int x)
  requires x <E @Lo
  ensures res <E @Hi;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branch3_safe(int x)
  requires x <E @Hi
  ensures res <E @Lo;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branch4_safe(int x)
  requires x <E @Hi
  ensures res <E @Hi;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branchS1_safe(int x)
  requires true
  ensures res <E @Lo;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branchS2_safe(int x)
  requires true
  ensures res <E @Hi;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_branchS3_safe(int x)
  requires true
  ensures res <E x;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}
