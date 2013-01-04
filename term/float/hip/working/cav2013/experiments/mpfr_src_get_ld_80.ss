void mpfr_src_get_ld_80()
{
  float r;
  int sh;
  while (r < 1.0)
    case {
      r <= 0.0       -> requires Loop ensures false;
      0.0 < r <  1.0 -> requires Term[Seq{-r @ (-infty,0.0), r < 1.0}] ensures true;
      r >= 1.0       -> requires Term[] ensures true;
    }
  {
    r += r;
    sh--;
  }
}
