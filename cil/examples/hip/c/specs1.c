int foo0()
{
  return 1;
}

int foo1()
/*@
  requires true 
  ensures res > 0;
*/
{
  return 1;
}

int foo2()
/*@
  requires true 
  ensures res < 0;
*/
{
  return 1;
}

int foo3()
/*@
  requires true 
  ensures true;
*/
{
  return 1;
}

int foo4()
/*@
  requires true 
  ensures false;
*/
{
  return 1;
}
