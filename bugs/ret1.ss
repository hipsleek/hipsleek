
int foo (int n)
  requires true
  ensures res>3;
{
  if (n>0)
    return 1;
  else return 2;
}

