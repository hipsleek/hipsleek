void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x > 10) return;
  else return f(x + y, x - y);
}
