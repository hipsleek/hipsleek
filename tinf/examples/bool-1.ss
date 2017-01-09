void f(int x, bool b)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (b) f(x - 1, b);
    else f(x + 1, b);
  }
}