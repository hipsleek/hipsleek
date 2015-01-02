void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x - 1);
}

void g(int x) 
  infer [@term]
  requires true
  ensures true;
{
  f(x);
}
