void f (int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else g(x);
}

void g (int z)
  infer [@term]
  requires true
  ensures true;
{
  if (z < 0) return;
  else f(z - 1, 0);
}
