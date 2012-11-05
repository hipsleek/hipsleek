//

void loop(float x, float y)
  case
  {
    x <= 0.0 | y <= 0.0  -> requires Term[] ensures true;
    x >  0.0 & y >  0.0  ->
      case
      {
        y/x >= 0.1 -> requires Term[] ensures true;
        y/x <  0.1 ->
          case
          {
            y <= 1.0     -> requires Loop ensures false;
            1 < y <= 2.0 -> requires Term[1, Seq{-y @ (-infty, -1), y<=2.0}] ensures true;
            y >  2.0     -> requires Term[0, Seq{-y/x @ (-infty, 0), y/x<0.1}] ensures true;
          }
      }
  }
{
  if ((x>0.0) && (y>0.0)) 
  {
    if (y/x < 0.1)
    {
      float y1 = y*y;
      float x1 = 2.0*x;
      loop(x1,y1);
    }
  }
}
