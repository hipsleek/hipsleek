float loop(float x)
  case {
    x > 0.0 -> requires Term[SeqConDec(x, 0.0, x <= 0.1)] ensures true;
    x <= 0.0 -> requires Term[] ensures true;
  }
  
{
  if (x > 0.0)
    return loop(x/2.0);
  else
    return x;
}
