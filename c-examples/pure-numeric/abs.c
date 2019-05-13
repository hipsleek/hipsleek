/*@
relation A(int n).
*/

int abs (int i)
/*@
  infer [A]
  requires true
  ensures A(res);
*/
{
  return i < 0 ? -i : i;
}
