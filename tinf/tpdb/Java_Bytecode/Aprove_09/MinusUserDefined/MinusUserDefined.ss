bool gt(int x, int y) 
  //requires x >= 0 & y >= 0
  requires Term
  case {
    x <= 0 -> ensures !res;
    x > 0 -> case {
      x > y -> ensures res;
      x <= y -> ensures !res;
    }
  }
{
  while (x > 0 && y > 0) 
    case {
      x <= 0 -> requires Term ensures x' = x & y' = y;
      x > 0 -> case {
        y <= 0 -> requires Term ensures x' = x & y' = y;
        y > 0 -> case {
          x > y -> requires Term[y] ensures x' > 0 & y' = 0;
          x <= y -> requires Term[x] ensures x' = 0 & y' >= 0;
        }
      }
    }
  {
    x--;
    y--;
  }
  return x > 0;
}

int random() 
  requires Term
  ensures res >= 0;


void main() 
  requires Term
  ensures true;
{
  int x = random();
  int y = random();
  int rs = 0;

  while (gt(x,y)) 
    case {
      x <= 0 -> requires Term ensures x' = x & y' = y & rs' = rs;
      x > 0 -> case {
        x > y -> requires Term[x - y] ensures x' = x & y' = x;
        x <= y -> requires Term ensures x' = x & y' = y & rs' = rs;
      }
    }
  {
    y++;
    rs++;
  }
}
