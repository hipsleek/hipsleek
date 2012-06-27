float loop(float x)
  case {
    x <= 0 -> requires Term[] ensures true;
    x > 0 -> requires Term[SeqConDec(x, 0.1, x < 0.1)] ensures true;          // Fail because of invalid fixpoint
  }
{
  if (x > 0.1)
    return loop(x/2.0);
  else
    return x;
}
