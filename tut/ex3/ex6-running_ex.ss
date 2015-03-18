void loop (int x, int y)
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> case {
      y >= 0 -> requires Loop ensures false;
      y < 0 -> requires Term[x] ensures true;
    }
  }
{
  if (x < 0) return;
  else loop(x+y, y);
}
