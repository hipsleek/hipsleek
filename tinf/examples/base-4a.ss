void f(int x)
  infer [@term]
  requires x > 0
  ensures true;
{
  if (x <= 0) return;
  else f(x + 1);
}