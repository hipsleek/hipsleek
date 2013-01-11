void fftw_libbench2_mp_55()
{
  float RADIX = 65536.0;
  float IRADIX = (1.0 / RADIX);
  int e;
  float x;
  while (x < IRADIX)
    case {
      (RADIX != 65536.0) | (IRADIX != 1.0/RADIX) -> 
                requires false ensures false;
      (RADIX  = 65536.0) & (IRADIX  = 1.0/RADIX) & (x >= IRADIX) ->
                requires Term[] ensures true;
      (RADIX  = 65536.0) & (IRADIX  = 1.0/RADIX) & (0 < x < IRADIX) ->
                requires Term[Seq{-x@(-infty,0), x < IRADIX}] ensures true;
      (RADIX  = 65536.0) & (IRADIX  = 1.0/RADIX) & (x <= 0) ->
                requires Loop ensures false;
    }
  {
    x *= RADIX;
    --e; 
  }
}
