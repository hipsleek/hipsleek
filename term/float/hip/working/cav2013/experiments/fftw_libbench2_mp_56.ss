void fftw_libbench2_mp_55()
{
  float RADIX = 65536.0;
  float IRADIX = (1.0 / RADIX);
  int e;
  float x;
  while (x < IRADIX)
    requires (0.0 < IRADIX < 1.0) & (RADIX > 1.0)
    case {
      x >= IRADIX    -> requires Term[] ensures true;
      0 < x < IRADIX -> requires Term[Seq{-x@(-infty,0), x < IRADIX}] ensures true;
      x <= 0         -> requires Loop ensures true;
    }
  {
    x *= RADIX;
    --e; 
  }
}
