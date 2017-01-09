void loop(int x, int y)
  case {
    x <= y -> requires Term ensures true;
    x > y -> case {
      x < 0 -> requires Loop ensures false;
      x >= 0 -> requires MayLoop ensures true;
    }
  }
{
  if (x <= y) return;
  else loop(x-1, x+y);
}
