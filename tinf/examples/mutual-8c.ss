void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x);
}

void g(int x) 
  infer [@term]
  requires true
  ensures true;
{
  f(x + 1);
}
