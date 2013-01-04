float fabs(float x)
  requires Term[]
  ensures res = __abs(x);

void gsl_sys_ldfrexp_101 (float f)
{
  int ei = 0;
  while (fabs (f) > 0 && fabs (f) < 0.5)
    case {
      f >= 0.5     -> requires Term[] ensures true;
      0 < f < 0.5  -> requires Term[Seq{-f @ (-infty,0), 0 < __abs(f) < 0.5}] ensures true;
      f = 0        -> requires Term[] ensures true;
      -0.5 < f < 0 -> requires Term[Seq{f @ (-infty,0), 0 < __abs(f) < 0.5}] ensures true;
      f <= -0.5    -> requires Term[] ensures true;
    }
  {
    ei--;
    f *= 2.0;
  }
}

