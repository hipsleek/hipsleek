int f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return g(x);
}

int g(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return f(x + 1);
}
