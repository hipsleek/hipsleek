void f(int x) {
  if (x <= 1) return;
  else {
    int old_x = x;
    x = __VERIFIER_nondet_int();
    //assume x' >= 2*old_x';
    if (x < 2*old_x) return;
    else {
      // assert x' >= 2; // ok
      f(x);
    }
  }
}
