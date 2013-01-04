void mpfr_tests_tset_ld_256 ()
{
  float d;
  float LDBL_MAX;
  while (d < LDBL_MAX/2.0)
    requires LDBL_MAX > 0.0 & d > 0
    case {
      d < LDBL_MAX/2.0  -> requires Term[Seq{-d @ (-infty, 0), d < LDBL_MAX/2.0}]
                           ensures true;
      d >= LDBL_MAX/2.0 -> requires Term[]
                           ensures true;
    }
  {
    d += d;
  }
}
