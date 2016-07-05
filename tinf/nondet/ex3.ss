void f(int x) {
  if (x < 0) return;
  else {
    if (__VERIFIER_nondet_int() > 0)
      f(x - 1);
    else
      f(x - 2);
  }
}
