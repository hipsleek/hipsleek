float sqrt(float x)
  requires x >= 0.0 & Term[]
  ensures res = __sqrt(x);

float foo(float x)
  case {
    x <= 1.1 -> requires Term[]
                ensures true;
    x >  1.1 -> requires Term[Seq{x @ (1.0, +infty),  1.1}]
                ensures true;
  }
{
  if (x > 1.1)
  {
    float y = sqrt(x);
    return foo(y);
  }
  else
    return x;
}
