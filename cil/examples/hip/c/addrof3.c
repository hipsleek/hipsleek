int foo ()
{
  int *p;
  int z;
  z = 1;
  p = &z;
  z= 3;
  int *q = &z;
  return 1;
}

void main ()
{
  return;
}
