void nd_loop(int x)
  infer [@term]
  requires true
  ensures true;
{
  int a = __VERIFIER_nondet_int();
  assume a > 0;
  if (x < 0 && a > 0) {
    int b = __VERIFIER_nondet_int();
    //assume b' <= 0;
    nd_loop(x + b);
    //nd_loop(x + __VERIFIER_nondet_int());
  }
  else return;
}
