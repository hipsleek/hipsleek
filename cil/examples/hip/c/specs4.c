int foo1()
{
  return 1;
}

int foo2()
/*@ */
{
  return 1;
}

int foo3()
/*@      */
{
  return 1;
}
