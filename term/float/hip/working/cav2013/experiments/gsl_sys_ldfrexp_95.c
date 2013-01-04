/*@
  float abs(float x)
    requires Term
    ensures res = __abs(x);
*/

void gsl_sys_ldfrexp_95 (float f)
{
  int ei = 0;
  while (fabs(f) >= 1.0)
  {
    ei++;
    f /= 2.0;
  }
}

