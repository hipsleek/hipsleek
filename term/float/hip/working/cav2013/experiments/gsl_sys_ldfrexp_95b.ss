float fabs(float x)
  requires Term[]
  ensures res = __abs(x);

void gsl_sys_ldfrexp_95 (float f)
{
  int ei = 0;
  while (fabs(f) >= 1.0)
    case {
      __abs(f) >= 1.0 -> requires Term[Seq{__abs(f) @ (0,+infty), __abs(f) >= 1.0}] ensures true;
      __abs(f) <  1.0 -> requires Term[] ensures true;
    }
  {
    ei++;
    f /= 2.0;
  }
}

