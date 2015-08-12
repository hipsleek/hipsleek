void loop(int x, int tx) {
  if (x>=0 && x <= tx) {
    tx = x - 1;
    x = __VERIFIER_nondet_int();
    loop(x, tx);
  }
}
