/* Example suggested by Shengchao */

void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else f(x + y, x + y);
}