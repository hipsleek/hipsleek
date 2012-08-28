float loop(float x)
  requires Term[SeqDec{x, -0.1, x <= 0.0}] ensures true;     // Bug
{
  if (x > (0.0))
    return loop(x/2.0);
  else
    return x;
}
