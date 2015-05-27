void nd_loop(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x >= 0 && __VERIFIER_nondet_int() > 0) return;
  else nd_loop(x + 1);
}

