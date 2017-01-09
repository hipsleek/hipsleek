void loop(int x, int y)
  case {
    x <= y -> requires Term ensures true;
    x > y -> case {
      x <= 1 -> requires Term[1 - x] ensures true;
      x > 1 -> requires Term[x - y] ensures true;
    }
  }
{
  if (x <= y) return;
  else loop(x+1, x+y);
}
