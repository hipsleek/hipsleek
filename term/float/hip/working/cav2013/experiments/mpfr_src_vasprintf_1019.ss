void mpfr_src_vasprintf_1019()
{
  float x;
  while (x > 9.0)
    case {
      x <= 9.0 -> requires Term[] ensures true;
      x >  9.0 -> requires Term[Seq{x @ (0, +infty), x > 9.0}] ensures true;
    }
  {
    x /= 10.0;
  }
}
