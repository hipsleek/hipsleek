void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x, y);
}

void g(int x, int y) 
  infer [@term]
  requires true
  ensures true;
{
  f(x + y, y - 1);
}
