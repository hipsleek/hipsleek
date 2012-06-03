float loop(float x)
  case {
    x <= 0.1 -> requires Term[] ensures true;
    x > 0.1 -> requires Term[SeqConDec(x, 0.0, sqrt(0.2))] ensures true;
  }
{
  if (x > (0.1))
    return loop(x/2.0);
  else
    return x;
}
