void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x, y - 1);
}

void g(int x, int y) 
  infer [@term]
  requires true
  ensures true;
{
  f(x + y, y);
}
