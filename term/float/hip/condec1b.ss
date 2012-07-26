float loop(float x)
  case {
    x <= 0.1 -> requires Term[] ensures true;
    x > 0.1 -> requires Term[SeqDec(x, 0.1, x < 0.1)] ensures true;          // Fail because of invalid limit
  }
{
  if (x > 0.1)
    return loop(x/2.0);
  else
    return x;
}
