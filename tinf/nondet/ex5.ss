void f(int x, int y)
{
  if (x < 0) return;
  else if (__VERIFIER_nondet_int() > 0)
    f(x+x+y, y+1);
  else f(x-1, y);
}

void g(int x, int y)
{
  if (x < 0) return;
  else
    g(x+x+y, y+1);
}
