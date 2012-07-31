float loop(float x)
  case {
    x >= 0.0 -> requires Loop ensures true;
    x < 0.0  -> requires Term[SeqDec{x, -infinity, x < 0.0 -100.0}] ensures true;
  }
{
  if (x < (0.0 - 100.0))
    return x;
  else
    return loop(x * (0.0-2.0));
}q
