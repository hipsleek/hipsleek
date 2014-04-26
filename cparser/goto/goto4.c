int foo(int i)
/*@
  requires i = 0
  ensures res = 2;
*/
{
  while (i < 2)
    /*@
      requires i = 0
      ensures i' = 2;
    */
    {
      goto label1;
      i = i + 1;
    label1: i = i + 2;
    }
  return i;
}
