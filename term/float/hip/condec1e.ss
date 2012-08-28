float loop(float x)
  case {
    x >= 0.1          -> requires Term[] ensures true;
    0.0 < x & x < 0.1 -> requires Term[SeqDec{x, 0.0, x > 0.1}] ensures true;
    x == 0.0          -> requires Loop ensures true;
    x < 0.0           -> requires Term[SeqDec{-x, 0.0, x > 0.1}] ensures true;
  }
{
  if (x < 0.1)
    return loop(x/2.0);
  else
    return x;
}
