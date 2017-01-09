void main() 
  requires MayLoop
  ensures true;
{
  int x;
  int y;
  
  while (x > 0) 
    case {
      x <= 0 -> requires Term ensures x' = x & y' = y;
      x > 0 -> requires Loop ensures false;
    }
  {
    x++;
    y = x;
    while (y > 0) 
      case {
        y <= 0 -> requires Term ensures y' = y;
        y > 0 -> requires Term[y] ensures y' = 0;
      }
    {
      y--;
    }
  }
}
