int foo(int i)
/*@
  requires i = 0
  ensures res = 2;
*/
{
  goto label1;
  i = i + 1;
 label1: i = i + 2;
  return i;
}
