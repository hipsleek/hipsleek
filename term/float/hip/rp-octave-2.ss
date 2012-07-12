/*
  File: octave-3.6.2/libgnu/randpoisson.c
*/


/********************
  Line 441:
  if (L < 0.0) ret = NAN;
  else if (L <= 12.0) {
    // From Press, et al. Numerical recipes
    double g = exp(-L);
    int em = -1;
    double t = 1.0;
    do {
      ++em;
      t *= RUNI;
    } while (t > g);
    ret = em;
  }
*/

// 0 <= L <= 12; g = exp(-L)
// => 1 >= g >= 0.000006144
// 0 < RUNI < 1

void loop1 (float t, float g, float runi)
  case
  {
    !((0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0)) ->
        requires Term[] ensures true;
    ((0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0)) & t <= 0.0 ->
        requires Term[] ensures true;
    (0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0) & t > 0.0 ->
        requires Term[SeqConDec(t, 0.0, g)] ensures true;
  }
{
  if ((0.0 < runi) && (runi < 1.0) && (g >= 0.000006144) && (g <= 1.0))
  {
    if (t > g)
    {
      loop1(t * runi, g, runi);
    }
  }
  return;
}

void loop2 (float t, float g, float runi)
  case
  {
    !((0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0)) ->
        requires Term[] ensures true;
    ((0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0)) & t <= 0.0 ->
        requires Term[] ensures true;
    (0.0 < runi) & (runi < 1.0) & (g >= 0.000006144) & (g <= 1.0) & t > 0.0 ->
        requires Term[SeqConDec(t, 0.0, t <= g)] ensures true;
  }
{
  if ((0.0 < runi) && (runi < 1.0) && (g >= 0.000006144) && (g <= 1.0))
  {
    if (t > g)
    {
      loop2(t * runi, g, runi);
    }
  }
  return;
}
