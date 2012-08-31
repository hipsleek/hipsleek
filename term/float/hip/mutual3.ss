void fff(float x)
  case {
    x < 0.1 -> requires Term ensures true;
    x >= 0.1  -> requires Term[Seq{x, (0.0, +infty), 0.1}] ensures true;
  }
{
  if (x >= 0.1) fff(x/2.0);
}

