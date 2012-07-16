float fabs(float x)
  requires true ensures res >= 0;
{
  if (x >= 0)
    return x;
  else
    return -x;
}

// WORKED
void loop (float x)
  case
  {
    -0.1 <= x <= 0.1  -> requires Term[] ensures true;
    x > 0.1 -> requires Term[SeqConDec(x, 0, x < 0.1)] ensures true;
    x < -0.1 -> requires Term[SeqConDec(-x, 0, x <= 0.1)] ensures true;
  }
{
  if (x > 0.1)
    loop(x / 2.0);
  else if (x < -0.1)
    loop(x / 2.0);
}  

