int max2(int x, int y)
  requires true
  ensures res = k & k = max(x, y);

relation F(int x).
relation G(int x).
int f(int x, int y)
  infer [F,G]
  requires x <= 0 & F(y)
  ensures G(res);
{
  return max2(x, y);
}

int g(int x, int y)
  infer [F,G]
  requires x <? #@Lo & F(y)
  ensures G(res);
{
  return x + y;
}
