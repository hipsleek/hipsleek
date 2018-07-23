int equal_branch1_safe(int x)
  requires x <? @Lo
  ensures res <? @Lo;
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
  requires x <? @Lo
  ensures res <? @Hi;
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
  requires x <? @Hi
  ensures res <? @Lo;
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
  requires x <? @Hi
  ensures res <? @Hi;
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
  ensures res <? @Lo;
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
  ensures res <? @Hi;
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
  ensures res <? x;
{
  int y = x;
  if(x == 0) {
    y = 2;
  } else {
    y = 2;
  }
  return y;
}

int equal_single_branch1_safe(int x)
  requires x <? @Lo
  ensures res=0 & res <? @Lo;
{
  int y = 0;
  if(x > 0) {
    y = 0;
  }
  return y;
}

int equal_single_branch2_safe(int x)
  requires x <? @Lo
  ensures res=0 & res <? @Hi;
{
  int y = 0;
  if(x > 0) {
    y = 0;
  }
  return y;
}

int equal_single_branch3_safe(int x)
  requires x <? @Hi
  ensures res=0 & res <? @Lo;
{
  int y = 0;
  if(x > 0) {
    y = 0;
  }
  dprint;
  return y;
}

int equal_single_branch4_safe(int x)
  requires x <? @Hi
  ensures res=0 & res <? @Hi;
{
  int y = 0;
  if(x > 0) {
    y = 0;
  }
  return y;
}
