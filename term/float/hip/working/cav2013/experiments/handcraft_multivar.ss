void handcraft_multivar1()
{
  float x,y;
  while ((x > 0.0) && (y > 0.0) && (y/x < 0.1))
    case {
      x < 0.0 -> requires Term[] ensures true;
      x = 0.0 -> requires false ensures false;
      x > 0.0 ->
        case {
          y < 0.0 -> requires Term[] ensures true;
          y = 0.0 -> requires false ensures false;
          y > 0.0 ->
            case {
              y/x >= 0.1 -> requires Term[] ensures true;
              y/x <  0.1 ->
                case {
                  y <= 1.0     -> requires Loop ensures false;
                  1 < y <= 2.0 -> requires true ensures true;
                  y > 2.0      -> requires Term[Seq{-y/x @ (-infty,0), y/x<0.1}] ensures true;
                }
            }
        }
    }
  {
    y = y*y;
    x = 2.0*x;
  }
}
