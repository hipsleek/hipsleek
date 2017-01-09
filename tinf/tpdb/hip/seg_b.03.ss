void loop (int x, int y)
/*
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires Loop ensures false;
  }
*/
{
  if (x < 0) return;
  else {
    loop(x + y, __VERIFIER_nondet_int());
    loop(x - y, __VERIFIER_nondet_int());
  }
}
