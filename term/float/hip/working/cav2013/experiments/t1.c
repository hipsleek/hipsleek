
void gsl_sys_ldfrexp_95 (float f)
{
  int ei = 0;
  while (f >= 1.0)
  /*@
    case
    {
      f >= 1.0 -> requires Term[Seq{f @ (0,+infty), f >= 1.0}] ensures true;
      f <  1.0 -> requires Term[] ensures true;
    }
  */
  {
    ei++;
    f /= 2.0;
  }
}

