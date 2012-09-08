//

void loop(float x, float y)
  case
  {
    x <= 0 | y <= 0                     -> requires Term[] ensures true;
    x > 0 & y > 0 & y/x >= 0.1          -> requires Term[] ensures true;
    x > 0 & y > 0 & y/x <  0.1 & y <= 1 -> requires Loop   ensures false;
    x > 0 & y > 0 & y/x <  0.1 & y > 2  -> requires Term[Seq{-y/x@(-infty, 0), -0.1}]   ensures true;
    x > 0 & y > 0 & y/x <  0.1 & 1 < y <=2  -> requires true  ensures true;
  }
{
  if ((x>0) && (y>0)) {
    if (y/x < 0.1)
    {
      float y1 = y*y;
      float x1 = 2*x;
      loop(x1,y1);
    }
  }
}
