void f(int x)
  infer [@term]
  requires x > -2
  ensures true;
{
  if (x <= 0) return;
  else f(x + 1);
}