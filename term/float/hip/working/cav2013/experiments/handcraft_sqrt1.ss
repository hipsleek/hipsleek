float sqrt(float x)
  requires x >= 0.0 & Term[]
  ensures res = __sqrt(x);

void handcraft()
{
  float x;
  while (x > 1.1)
    case {
      x <= 1.1 -> requires Term[]
                  ensures true;
      x >  1.1 -> requires Term[Seq{x @ (1.0, +infty),  1.1}]
                  ensures true;
    }
  {
    x = sqrt(x);
  }
}
