/*
  File: octave-3.6.2/libgnu/vasnprintf.c
*/


/********************
  Line 1346:
      // GMP_LIMB_BITS = 32
      if (!(y >= 0.0L && y < 1.0L))
        ...
      if (y == 0.0L)
        ...
      if (y < 0.5L)
      {
        while (y < (1.0L / (1 << (GMP_LIMB_BITS / 2)) / (1 << (GMP_LIMB_BITS / 2))))
          {
            y *= 1.0L * (1 << (GMP_LIMB_BITS / 2)) * (1 << (GMP_LIMB_BITS / 2));
            exp -= GMP_LIMB_BITS;
          }
        ...
      }
*/

// Use bound in Term specs
void loop1 (float y)
  case
  {
    y <= 0.0            ->  requires Term[] ensures true;
    y >= 0.5            ->  requires Term[] ensures true;
    y > 0.0 & y < 0.5   ->  requires Term[SeqDec(-y, -infinity, -1.0 / 65536.0 / 65536.0)] ensures true;
  }
{
  if (y <= 0.0)
    return;
  
  if (y >= 0.5)
    return;

  float d = 65536.0;   //  d = 1 << (GMP_LIMB_BITS/2)
  if (y < 1.0 / d / d)
    loop1( y * 1.0 * d * d);

  return;
}


// Use constraint in Term specs
void loop2 (float y)
  case
  {
    y <= 0.0            ->  requires Term[] ensures true;
    y >= 0.5            ->  requires Term[] ensures true;
    y > 0.0 & y < 0.5   ->  requires Term[SeqDec(-y, -infinity, y > 1.0 / 65536.0 / 65536.0)] ensures true;
  }
{
  if (y <= 0.0)
    return;
  
  if (y >= 0.5)
    return;

  float d = 65536.0;   //  d = 1 << (GMP_LIMB_BITS/2)
  if (y < 1.0 / d / d)
    loop2( y * 1.0 * d * d);

  return;
}

