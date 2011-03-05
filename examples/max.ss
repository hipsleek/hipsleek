// correct one
int max0(int x, int y)
 requires true
 ensures x >= y & res = x or x <= y & res = y;
{
  if (x > y)
    return x;
  else
    return y;
}

int max1(int x, int y)
 requires true
 ensures x >= y & res = x or x <= y & res = y;
{
  if (x > y) {
    return 1; // fail here
  } else {
    return y;
  }
}

int max2(int x, int y)
 requires true
 ensures x >= y & res = x or x <= y & res = y;
{
  if (x > y) {
    return x;
  } else {
    if (x == y) return 1; // fail here
    return y;
  }
}

int max3(int x, int y)
 requires true
 ensures x >= y & res = x or x <= y & res = y;
{
  if (x > y) {
    return 1; // fail here
  } else {
    return 1; // and here
  }
}
