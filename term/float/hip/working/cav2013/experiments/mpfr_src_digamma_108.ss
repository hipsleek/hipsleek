void mpfr_src_digamma_108 ()
{
  float e;
  float f;
  while (e > 1.0)
    case {
      e <= 1.0 -> requires Term[] ensures true;
      e >  1.0 -> requires Term[Seq{e @ (1.0, +infty), e > 1.0}] ensures true;
    }
  {
    f = f + 1.0;
    e = (e + 1.0) / 2.0;
  }
}
