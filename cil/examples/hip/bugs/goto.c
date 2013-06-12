int main()
{
  int a = 3;
  int b = 4;
  if (a > 2)
  {
    if ( b > 3) {
      return a;
    }
    else
      goto __Label;
  }
  else {
  __Label:
    a = 2;
    return a;
  }
}
