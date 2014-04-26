int foo(int i)
/*@
  requires true
  ensures res = 0;
*/
{
 label1:
  goto label1;
  return 0;
}
