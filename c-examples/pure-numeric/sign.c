/*@
relation R(int x).
*/

int sign(int x)
/*@
  infer [R]
  requires true
  ensures R(res);
*/
{
  if (x < 0) {
    return -1;
  }
  else if (x == 0)
  {
    return 0;
  }
  else
  {
    return 1;
  }
}


int signum(int x)
/*@
  infer [R]
  requires true
  ensures R(res);
*/
{
  return x < 0 ? -1 :
         x == 0 ? 0 :
                  1;
}
