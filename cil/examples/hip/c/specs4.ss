int foo1()
{
  return 1;
}

int foo2()
{
  return 1;
}
/*
 when no specs are given, we should use
   requires true
   ensures true;

 rather than requires false
             ensures false;
*/

int foo3()
  requires true
  ensures true;
{
  return 1;
}

