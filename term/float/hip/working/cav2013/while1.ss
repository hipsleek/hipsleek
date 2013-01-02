void foo()
{
  float x;
  while (x > 0.01)
    case {
      x > 0.01 -> requires Term[Seq{x @ (0,+infty), x>0.01}] ensures true;
      x <= 0.01 -> requires Term[] ensures true;
    }
  {
    x = x / 2.0;
  }
}
