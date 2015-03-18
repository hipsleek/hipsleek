/*
void loop(int x)
{
  if (x>=0 && (__VERIFIER_nondet_int() > 0)) {
    x = x - 1;
    loop(x);
  }
}
*/

global int nondet;

void loop(int x)
{
  if (x>=0 && nondet>0) {
    x = x - 1;
    loop(x);
  }
}
