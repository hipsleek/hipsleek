// don't need CASE specification to prove termination

float loop(float x)
  requires Term[Seq{x, 0.0, x <= 0.1}] ensures true;
{
  if (x > (0.1))
    return loop(x/2.0);
  else
    return x;
}

