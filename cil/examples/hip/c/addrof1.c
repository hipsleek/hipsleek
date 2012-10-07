int foo ()
{
  int *p;
  int z;
  z = 1;
  p = &z;
  int a[10];
  a[0] = 3;
  p = a[0];
  return *p;
}

void main ()
{
  return;
}
