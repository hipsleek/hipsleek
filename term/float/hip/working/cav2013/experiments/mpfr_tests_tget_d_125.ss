void mpfr_tests_tget_d_125 ()
{
  float d;
  float DBL_MAX;
  while (d < DBL_MAX/2.0)
    requires DBL_MAX > 0.0 & d > 0
    case {
      d < DBL_MAX/2.0  -> requires Term[Seq{-d @ (-infty, 0), d < DBL_MAX/2.0}]
                          ensures true;
      d >= DBL_MAX/2.0 -> requires Term[]
                          ensures true;
    }
  {
    d += d;
  }
}
