void loop (int x, int y)
{
  if (x < 0) return;
  else {
    loop(x + y, y);
    loop(x - y, y);
  }
}
