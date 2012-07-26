float loop(float x)
  case {
    x <= 0.1 -> requires Term[] ensures true;
    x > 0.1 -> requires Term[SeqDec(x, 0.0, x < 0.1)] ensures true;
  }
{
  if (x < 0.1)
    return x;
  else
    return loop(x/2.0);
}
