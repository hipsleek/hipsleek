template int r1(int x, int y).
template int r2(int x, int y).

void loop (int p, int q)
  infer [r1, r2]
  case {
    p > 0 & q > 0 -> case {
      q < p -> requires Term[r1(p,q)] ensures true;
      q >= p -> requires Term[r2(p,q)] ensures true;
    }
    !(p > 0 & q > 0) -> requires Term ensures true;
  }
{
  if (q > 0 && p > 0) {
    if (q < p) {
      q = q - 1;
      p = __VERIFIER_nondet_int();
    } else {
      p = p - 1;
      q = __VERIFIER_nondet_int();
    }
    loop(p, q);
  }
}
