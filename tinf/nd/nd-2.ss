void nd_loop(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0 && __VERIFIER_nondet_int() > 0) 
    nd_loop(x + __VERIFIER_nondet_int());
  else return;
}
