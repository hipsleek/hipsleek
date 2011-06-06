int foo(int a, int b)
{
  //int x = a / 2;
  //  x = div2(a,2);
  //x = div2(a,0);
  //int x = a / 2;
  int x = div2(a,0);
  //x = div3(a,0);
  return x;
}

int foo2(int a, int b)
  requires true
  ensures true;
{
  int x = div2(a,0);
  return x;
}

