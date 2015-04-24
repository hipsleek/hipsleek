void nd_loop(int x, int a)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0 && __VERIFIER_nondet_int() > 0) 
    nd_loop(x + a, a);
  else return;
}
