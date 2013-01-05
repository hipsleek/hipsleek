void mpfr_tests_tget_d_172 ()
{
  float d;
  float DBL_MIN;
  while (d < DBL_MIN * 2.0)
    requires DBL_MIN > 0.0 & d > 0.0
    case {
      d < DBL_MIN*2.0  -> requires Term[Seq{d @ (0.0,+infty), d < DBL_MIN*2.0}]
                          ensures true;
      d >= DBL_MIN*2.0 -> requires Term[]
                          ensures true;
    }
  {
    d /= 2.0;
  }
}

// BUG:
// Line 6: "requires DBL_MIN > 0.0 & d > 0.0" wasn't included???
