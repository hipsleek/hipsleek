void nd_loop(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x >= 0) {
    nd_loop(x + __VERIFIER_nondet_int());
  }
  else return;
}

/*
void nd_loop(int x, int nd)
  infer [@term]
  requires true
  ensures true;
{
  if (x >= 0) 
    nd_loop(x + nd, nd);
  else return;
}
*/
