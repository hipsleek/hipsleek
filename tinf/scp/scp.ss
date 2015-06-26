void loop (int x, int y)
{
  if (x > 0)
    loop(2*x+y, y-1);
}
