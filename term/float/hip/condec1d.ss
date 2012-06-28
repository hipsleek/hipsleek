float loop(float x)
  case {
    x <= 0.0 -> requires Term[] ensures true;
    x > 0.0 -> requires Term[SeqConDec(x, 0.0, x <= 0.0)] ensures true;   // fail because of invalid term constraint
  }
{
  if (x > 0.0)
    return loop(x/2.0);
  else
    return x;
}
