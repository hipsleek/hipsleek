void loop (int x, int y)
  requires true
  ensures true;
{
  if (x > 10) return;
  else loop(x+y, x-y);
}
