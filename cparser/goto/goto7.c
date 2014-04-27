int foo(int i)
/*@
  requires true
  ensures res = 0;
*/
{
  if (i == 0) {
  label1:
    i = i + 1;
    goto label1;
  } else {
    i = i + 2;
  }
  return 0;
}
