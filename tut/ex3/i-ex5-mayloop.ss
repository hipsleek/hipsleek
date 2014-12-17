void loop(int x, int y)
  infer[@term]
  requires true
  ensures true;
{
  if (x <= y) return;
  else loop(x-1, x+y);
}
