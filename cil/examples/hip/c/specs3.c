int foo1()
/*@
  requires true 
  ensures res > 0;
*/
{
  int x = 10;
  /*@ dprint; */
  return 1;
}

int foo2()
//@ requires true ensures res > 0;
{
  int x = 10;
  //@ dprint;
  return 1;
}
