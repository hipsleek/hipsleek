void loop(int x, int y)
{
  if (x>=0 && (__VERIFIER_nondet_int() > 0)) {
    x = x + y;
    loop(x, y);
  }
}
