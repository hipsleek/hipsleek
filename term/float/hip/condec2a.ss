float loop(float x)
  requires Term[SeqConDec(x, 0.0, 0.1)] ensures true;
{
  if (x > (0.0))
    return loop(x/2.0);
  else
    return x;
}
