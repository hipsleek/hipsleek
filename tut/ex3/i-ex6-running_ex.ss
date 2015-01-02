void loop (int x, int y)
  infer[@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else loop(x+y, y);
}
