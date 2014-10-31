void loop(int x)
  requires x>=0
  ensures true;
{
  if (__VERIFIER_nondet_int() > 0) {
    x = x + 1;
    loop(x);
  }
}

