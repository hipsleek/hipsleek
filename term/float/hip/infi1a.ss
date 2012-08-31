float loop(float x)
  case {
    x >= 0.0 -> requires Term[] ensures true;
    x < 0.0  -> requires Term[Seq{x, -infty, x < 0.0 -100.0}] ensures true;
  }
{
  if (x < (0.0 - 100.0))
    return x;
  else
    return loop(x * 2.0);
}
