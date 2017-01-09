void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x, 0);
}

void g(int x, int y) 
  infer [@term]
  requires true
  ensures true;
{
  f(x + y);
}
