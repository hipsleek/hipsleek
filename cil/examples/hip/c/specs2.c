int foo1()
/*@
  requires true 
  ensures res > 0;
*/
{
  int x = 10;
  /*@ assert x' < 11; */
  return 1;
}

int foo2()
/*@
  requires true 
  ensures res > 0;
*/
{
  int x = 10;
  /*@ assert x' > 11; */
  return 1;
}

int foo3()
//@ requires true ensures res > 0;
{
  int x = 10;
  //@ assert x' < 11;
  return 1;
}

int foo4()
//@ requires true ensures res > 0;
{
  int x = 10;
  //@ assert x' > 11;
  return 1;
}
