void fftw_libbench2_mp_55()
{
  float RADIX = 65536.0;
  float IRADIX = (1.0 / RADIX);
  int e;
  float x;
  while (x >= 1.0)
    requires (0 < IRADIX < 1)
    case {
      x <  1.0 -> requires Term[] ensures true;
      x >= 1.0 -> requires Term[Seq{x @ (0, +infty), x >= 1.0}] ensures true;
    }
  {
    x *= IRADIX;
    ++e; 
  }
}
