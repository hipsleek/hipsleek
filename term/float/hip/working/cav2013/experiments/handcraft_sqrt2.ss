float sqrt(float x)
  requires x >= 0.0 & Term[]
  ensures res = __sqrt(x);

void handcraft()
{
  float x;
  while ((x >= 0.0) && (x <= 0.9))
    case {
      x > 0.9        -> requires Term[] ensures true;
      0.0 < x <= 0.9 -> requires Term[Seq{-x @ (-1.0, 0), x <= 0.9}] ensures true;
      x = 0          -> requires Loop ensures false;
      x < 0          -> requires Term[] ensures true;
    }
  {
    x = sqrt(x);
  }
}
