float fabs(float x)
  requires Term[]
  ensures res = __abs(x);

void gsl_sys_ldfrexp_95 (float f)
{
  int ei = 0;
  while (fabs(f) >= 1.0)
    case {
      f >= 1.0        -> requires Term[Seq{f @ (0,+infty), __abs(f) >= 1.0}] ensures true;
      -1.0 < f <  1.0 -> requires Term[] ensures true;
      f <= -1.0       -> requires Term[Seq{-f @ (0,+infty), __abs(f) >= 1.0}] ensures true;
    }
  {
    ei++;
    f /= 2.0;
  }
}

