int k;
int n;

int foo ()
/*@
   requires true
   ensures  res < 0;
 */
{
  return k*k + n*n;
}
